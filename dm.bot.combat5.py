import asyncio
from base64 import b64encode
from dataclasses import dataclass, field
from datetime import datetime
import logging
from typing import Any, Literal, Optional, List, Dict
from enum import Enum, auto

import discord
from discord import app_commands, ui
from discord.app_commands import Choice
from discord.ext import commands
import httpx
from openai import AsyncOpenAI
import yaml

import json
import aiohttp
import re
import io

import math
import random

# chess and urllib.parse are not used in the provided RPG logic, but kept for completeness
# import chess
# import urllib.parse

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s: %(message)s",
)

VISION_MODEL_TAGS = ("gpt-4", "o3", "o4", "claude", "gemini", "gemma", "llama", "pixtral", "mistral", "vision", "vl")
PROVIDERS_SUPPORTING_USERNAMES = ("openai", "x-ai")

EMBED_COLOR_COMPLETE = discord.Color.dark_green()
EMBED_COLOR_INCOMPLETE = discord.Color.orange()
EMBED_COLOR_RPG = discord.Color.dark_magenta()


STREAMING_INDICATOR = " ⚪"
EDIT_DELAY_SECONDS = 1

MAX_MESSAGE_NODES = 500
DISCORD_MESSAGE_LIMIT = 2000

DISTANCE_LEVELS = ["extreme", "distant", "medium", "close", "grapple"]

def get_config(filename: str = "config.yaml") -> dict[str, Any]:
    with open(filename, encoding="utf-8") as file:
        return yaml.safe_load(file)

def split_text_into_chunks(text: str, limit: int = DISCORD_MESSAGE_LIMIT) -> List[str]:
    if len(text) <= limit:
        return [text]
    chunks = []
    while text:
        if len(text) <= limit:
            chunks.append(text)
            break
        split_pos = text.rfind('\n', 0, limit)
        if split_pos == -1:
            split_pos = text.rfind(' ', 0, limit)
        if split_pos == -1:
            split_pos = limit
        chunks.append(text[:split_pos].strip())
        text = text[split_pos:].strip()
    return [chunk for chunk in chunks if chunk]

config = get_config()
curr_model = next(iter(config["models"]))
system_prompt = config["system_prompt"]

msg_nodes = {}
last_task_time = 0

intents = discord.Intents.default()
intents.message_content = True
activity = discord.CustomActivity(name=(config["status_message"] or "github.com/jakobdylanc/llmcord")[:128])
discord_bot = commands.Bot(intents=intents, activity=activity, command_prefix=None)

rpg_sessions: dict[int, 'RPGSession'] = {}
httpx_client = httpx.AsyncClient()




def is_authorized():
    async def predicate(interaction: discord.Interaction) -> bool:
        permissions = config.get("permissions", {})
        allowed_user_ids = permissions.get("users", {}).get("allowed_ids", [])
        allowed_channel_ids = permissions.get("channels", {}).get("allowed_ids", [])

        if not allowed_user_ids and not allowed_channel_ids:
            return True
        if interaction.user.id in allowed_user_ids:
            return True
        if interaction.guild is not None and interaction.channel_id in allowed_channel_ids:
            return True
        return False

    return app_commands.check(predicate)

@discord_bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.CheckFailure):
        await interaction.response.send_message("⚠️ You do not have permission to use this command.", ephemeral=True)
    else:
        logging.error(f"An unhandled error occurred: {error}")
        if interaction.response.is_done():
            await interaction.followup.send("❌ An unexpected error occurred.", ephemeral=True)
        else:
            await interaction.response.send_message("❌ An unexpected error occurred.", ephemeral=True)

@dataclass
class MsgNode:
    text: Optional[str] = None
    images: list[dict[str, Any]] = field(default_factory=list)
    role: Literal["user", "assistant"] = "assistant"
    user_id: Optional[int] = None
    has_bad_attachments: bool = False
    fetch_parent_failed: bool = False
    parent_msg: Optional[discord.Message] = None
    lock: asyncio.Lock = field(default_factory=asyncio.Lock)
    
@dataclass
class CombatStats:
    initiative: int
    hit_points: int
    magic_points: int
    melee_attack: int
    ranged_attack: int
    magic_attack: int
    miracle_attack: int
    grapple_attack: int 
    physical_defense: int
    magic_defense: int
    
@dataclass
class GearItem:
    item_type: str
    description: str
    quality: str
    bonus: int
    target_stat: Optional[str] = None
    special_effect: Optional[str] = None

@dataclass
class CombatParticipant:
    name: str
    description: str
    distance: Literal["extreme", "distant", "medium", "close", "grapple"]
    is_boss: bool
    stats: Dict[str, int]
    combat_stats: CombatStats

@dataclass
class CombatState:
    participants: List[CombatParticipant] = field(default_factory=list)
    bystanders: List[str] = field(default_factory=list)
    turn: int = 1


class RPGState(Enum):
    IDLE = auto()
    AWAITING_ROLL = auto()
    AWAITING_STAT_ACTION_INPUT = auto()
    AWAITING_DESCRIPTION = auto()
    SETUP = auto()
    COMBAT = auto()

STAT_NAMES = ["STR", "DEX", "CON", "INT", "WIS", "CHA"]

@dataclass
class RPGSession:
    user_id: int
    user_mention: str
    stats: dict[str, int]
    story: list[dict[str, str]]
    combat_stats: Optional['CombatStats'] = None
    inventory: List[GearItem] = field(default_factory=list)
    combat_module_enabled: bool = False
    plot_outline: Optional[Dict[str, Any]] = None
    dm_personality: Optional[str] = None
    state: RPGState = RPGState.IDLE
    pending_action_text: Optional[str] = None
    pending_stat_for_action: Optional[str] = None
    pending_cv: Optional[int] = None
    pending_dv: Optional[int] = None
    pending_fv: Optional[int] = None
    pending_fv_details: Optional[str] = None
    combat_state: Optional['CombatState'] = None
    
# --- START: NEW HELPER FUNCTION ---
async def _get_llm_combat_narration(session: RPGSession, client: AsyncOpenAI, model: str, narration_prompt: str) -> str:
    """Gets a brief, dynamic combat narration from the LLM."""
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})
    
    # We use a limited history to keep the context focused on combat
    combat_story_history = session.story[-10:] 

    payload = plot_context + combat_story_history + [{"role": "system", "content": narration_prompt}]
    payload = _add_dm_personality_to_payload(session, payload)

    try:
        response = await client.chat.completions.create(model=model, messages=payload, stream=False, temperature=1.1, max_tokens=150)
        return response.choices[0].message.content.strip()
    except Exception as e:
        logging.error(f"Error during LLM combat narration: {e}")
        return "The battlefield is a chaotic blur of action!"

# --- END: NEW HELPER FUNCTION ---


def _add_dm_personality_to_payload(session: 'RPGSession', payload: list[dict[str, Any]], force_vanilla: bool = False) -> list[dict[str, Any]]:
    if session.dm_personality and not force_vanilla:
        personality_prompt = {"role": "system", "content": session.dm_personality}
        return [personality_prompt] + payload
    return payload
    
async def _check_if_combat_is_needed(
    client: AsyncOpenAI, model: str, session: RPGSession, action_text: str, extra_context: List[Dict[str,str]] = None
) -> bool:
    prompt = (
        "Based on the story so far and the player's latest action, does this action necessitate the start of a "
        "turn-based combat encounter? The story should only proceed to combat if it is an unavoidable and direct "
        f"consequence of this action: '{action_text}'. Respond with only a single word: YES or NO."
    )
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})
    
    story_history = session.story + (extra_context or [])
    
    payload = plot_context + story_history + [{"role": "system", "content": prompt}]
    try:
        response = await client.chat.completions.create(model=model, messages=payload, stream=False, temperature=0, max_tokens=5)
        result = response.choices[0].message.content.strip().upper()
        return "YES" in result
    except Exception as e:
        logging.error(f"Error during LLM combat check: {e}")
        return False

def _update_distance(current_distance: str, steps: int) -> str:
    try:
        current_index = DISTANCE_LEVELS.index(current_distance)
    except ValueError:
        return current_distance
    new_index = current_index - steps
    new_index = max(0, min(3, new_index))
    return DISTANCE_LEVELS[new_index]

# --- START: MODIFIED/NEW COMBAT UI VIEWS ---

class MeleeActionView(discord.ui.View):
    def __init__(self, session: 'RPGSession', target: 'CombatParticipant'):
        super().__init__(timeout=180)
        self.session = session
        self.target = target

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("This is not your turn!", ephemeral=True)
            return False
        return True

    async def end_player_turn(self, interaction: discord.Interaction, message: str):
        """Disables buttons, sends a final message, and prepares for the next turn."""
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(content=message, view=self)
        # In a full loop, this would trigger the NPC turn logic.
        # For now, we just end it.
        
    @discord.ui.button(label="Melee Attack", style=discord.ButtonStyle.danger)
    async def melee(self, interaction: discord.Interaction, button: discord.ui.Button):
        # 1. Calculate DV
        dv = 5 + self.target.combat_stats.physical_defense

        # 2. Get player's melee weapon quality
        weapon_quality = 0
        weapon_item = next((item for item in self.session.inventory if item.item_type == "Melee Weapon"), None)
        if weapon_item:
            weapon_quality = weapon_item.bonus

        # 3. Roll for the attack
        dice = await _roll_dice(4)
        if not dice or len(dice) < 4:
            await self.end_player_turn(interaction, "❌ Error rolling dice for melee attack.")
            return
            
        roll_val = (dice[0] + dice[1]) - (dice[2] + dice[3])
        av = roll_val + weapon_quality
        margin = av - dv

        # 4. Determine Outcome (Erratic Failure, Miss, Hit, Erratic Success)
        outcome_message = ""
        provider, model = curr_model.split("/", 1)
        client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

        if margin < -7: # Erratic Failure
            damage_to_player = max(1, weapon_quality)
            self.session.combat_stats.hit_points -= damage_to_player
            prompt = f"The player attempted a melee attack against {self.target.name} and it was an ERRATIC FAILURE. The player's weapon quality is {weapon_quality:+}. Narrate a brief, disastrous moment where the player messes up and accidentally hurts themselves for {damage_to_player} damage."
            narration = await _get_llm_combat_narration(self.session, client, model, prompt)
            outcome_message = f"**💥 ERRATIC FAILURE!**\n*{narration}*\nYou take **{damage_to_player}** damage! Your HP is now {self.session.combat_stats.hit_points}."
        
        elif av <= dv: # Miss
             outcome_message = f"You swing at **{self.target.name}**... and miss! (`AV {av}` vs `DV {dv}`)"

        else: # Hit or Erratic Success
            damage = max(1, weapon_quality)
            if margin > 7: # Erratic Success
                damage *= 2
                prompt = f"The player's melee attack against {self.target.name} was an ERRATIC SUCCESS. The player's weapon quality is {weapon_quality:+}. Narrate a brief, spectacular attack that deals double damage ({damage} total)."
                narration = await _get_llm_combat_narration(self.session, client, model, prompt)
                outcome_message = f"**✨ ERRATIC SUCCESS!**\n*{narration}*\nYou hit **{self.target.name}** for **{damage}** damage!"
            else: # Normal Hit
                outcome_message = f"You hit **{self.target.name}** for **{damage}** damage! (`AV {av}` vs `DV {dv}`)"

            self.target.combat_stats.hit_points -= damage
            if self.target.combat_stats.hit_points <= 0:
                outcome_message += f"\n**{self.target.name} has been defeated!**"
                self.session.combat_state.participants.remove(self.target)

        await self.end_player_turn(interaction, outcome_message)


    @discord.ui.button(label="Grapple", style=discord.ButtonStyle.secondary, disabled=True)
    async def grapple(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.end_player_turn(interaction, "Grapple logic is not yet implemented. Your turn ends.")

    @discord.ui.button(label="Point Blank", style=discord.ButtonStyle.secondary, disabled=True)
    async def point_blank(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.end_player_turn(interaction, "Point Blank logic is not yet implemented. Your turn ends.")


class ConfirmAttackView(discord.ui.View):
    def __init__(self, user_id: int, attack_type: Literal["Ranged", "Melee"]):
        super().__init__(timeout=180)
        self.user_id = user_id
        self.choice: Optional[bool] = None
        self.children[0].label = f"Yes, make a {attack_type} Attack"
        self.children[1].label = f"No, do not make a {attack_type} Attack"

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your turn!", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Yes", style=discord.ButtonStyle.success)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = True
        for item in self.children: item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()

    @discord.ui.button(label="No", style=discord.ButtonStyle.danger)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = False
        for item in self.children: item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()

class MovementView(discord.ui.View):
    def __init__(self, user_id: int):
        super().__init__(timeout=180)
        self.user_id = user_id
        self.choice: Optional[Literal["Jog", "Sprint"]] = None
        
    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your turn!", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Jog (Move 1 step)", style=discord.ButtonStyle.primary)
    async def jog(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = "Jog"
        for item in self.children: item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()

    @discord.ui.button(label="Sprint (Move 2 steps)", style=discord.ButtonStyle.secondary)
    async def sprint(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = "Sprint"
        for item in self.children: item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()

class PlayerCombatTurnView(discord.ui.View):
    def __init__(self, session: RPGSession):
        super().__init__(timeout=None)
        self.session = session
        
        participants = self.session.combat_state.participants
        for i, p in enumerate(participants):
            button = discord.ui.Button(
                label=f"{p.name} ({p.distance.title()})",
                style=discord.ButtonStyle.secondary,
                custom_id=f"combat_target_{i}",
                row=(i // 2)
            )
            button.callback = self.on_target_selected
            self.add_item(button)

    async def on_target_selected(self, interaction: discord.Interaction):
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("This is not your turn!", ephemeral=True)
            return
            
        for item in self.children:
            item.disabled = True
        await interaction.message.edit(view=self)

        target_index = int(interaction.data["custom_id"].split("_")[-1])
        target = self.session.combat_state.participants[target_index]
        
        # If target is already close, skip ranged/movement and go straight to melee options
        if target.distance == "close":
            action_view = MeleeActionView(self.session, target)
            await interaction.response.send_message(f"You are in close range of **{target.name}**. What is your move?", view=action_view, ephemeral=True)
            return # The MeleeActionView will handle the end of the turn

        # Ranged Attack phase
        if target.distance not in ["close", "grapple"]:
            ranged_attack_view = ConfirmAttackView(self.session.user_id, "Ranged")
            await interaction.response.send_message(f"You are targeting **{target.name}**. Do you want to make a Ranged Attack?", view=ranged_attack_view, ephemeral=True)
            await ranged_attack_view.wait()
            
            if ranged_attack_view.choice is True:
                await interaction.followup.send(f"You unleash a ranged attack at **{target.name}**! (Attack logic to be implemented). Your turn ends.", ephemeral=True)
                return
        
        # Movement phase
        movement_view = MovementView(self.session.user_id)
        send_method = interaction.followup.send if interaction.response.is_done() else interaction.response.send_message
        await send_method("How do you want to move?", view=movement_view, ephemeral=True)
        await movement_view.wait()
        
        if not movement_view.choice:
            await interaction.followup.send("You stood still, pondering your next move. Your turn ends.", ephemeral=True)
            return

        steps = 2 if movement_view.choice == "Sprint" else 1
        original_distance = target.distance
        target.distance = _update_distance(target.distance, steps)
        
        await interaction.followup.send(f"You {movement_view.choice.lower()} towards **{target.name}**, moving from {original_distance.title()} to {target.distance.title()}.", ephemeral=True)

        if movement_view.choice == "Sprint":
            await interaction.followup.send("After an all-out sprint, you catch your breath. Your turn ends.", ephemeral=True)
            return

        if movement_view.choice == "Jog" and target.distance == "close":
            # MODIFIED: Use MeleeActionView instead of ConfirmAttackView
            action_view = MeleeActionView(self.session, target)
            await interaction.followup.send(f"You are now in close range of **{target.name}**. What is your move?", view=action_view, ephemeral=True)
            return # The MeleeActionView will handle the end of the turn

        await interaction.followup.send("Your turn ends.", ephemeral=True)

# --- END: MODIFIED/NEW COMBAT UI VIEWS ---


GEAR_CATALOG = {
    "Melee Weapon": {"desc": "Adds a bonus to your **Melee Attacks**.", "target": "melee_attack"},
    "Ranged Weapon": {"desc": "Adds a bonus to your **Ranged Attacks**.", "target": "ranged_attack"},
    "Holdout Weapon": {"desc": "A concealed weapon that adds a bonus to your **Grapple Attacks**.", "target": "grapple_attack"},
    "Speed Enhancer": {"desc": "Footwear, a device, or an aura that increases your **Initiative**.", "target": "initiative"},
    "Magic Enhancer": {"desc": "A wand, focus, or component that adds a bonus to your **Magic Attacks**.", "target": "magic_attack"},
    "Miracle Enhancer": {"desc": "A holy symbol or relic that adds a bonus to your **Miracle Attacks**.", "target": "miracle_attack"},
    "Physical Armor": {"desc": "Shields, plating, or thick hides that add a bonus to your **Physical Defense**.", "target": "physical_defense"},
    "Magical Armor": {"desc": "Wards, charms, or resistant robes that add a bonus to your **Magical Defense**.", "target": "magic_defense"},
    "Special Trinket": {"desc": "A peculiar object with a strange, unpredictable effect determined by its nature.", "target": "special"},
    "Special Move": {"desc": "Your character's signature technique. You choose the bonus it applies to.", "target": "special"},
}

def _apply_gear_bonuses(session: RPGSession):
    if not session.combat_stats: return

    for item in session.inventory:
        if hasattr(session.combat_stats, item.target_stat):
            current_value = getattr(session.combat_stats, item.target_stat)
            setattr(session.combat_stats, item.target_stat, current_value + item.bonus)
            
async def _get_llm_trinket_effect(client: AsyncOpenAI, model: str, description: str) -> str:
    prompt = f"A player in an RPG has a 'Special Trinket' they described as: '{description}'. Invent a brief, strange, and mechanically simple passive effect for this item. The effect should be a single sentence. Be creative and weird. Example: 'Once per day, you can ask a single question to a nearby animal.' or 'This item hums faintly when a lie is told in your presence.'"
    try:
        response = await client.chat.completions.create(
            model=model, messages=[{"role": "system", "content": prompt}], temperature=1.2, max_tokens=60
        )
        return response.choices[0].message.content.strip()
    except Exception as e:
        logging.error(f"Error generating trinket effect: {e}")
        return "It feels oddly warm to the touch."

def _generate_npc_stats() -> Dict[str, int]:
    return {stat: random.randint(-1, 3) for stat in STAT_NAMES}

async def _initialize_combat(channel: discord.TextChannel, session: RPGSession, client: AsyncOpenAI, model: str):
    session.state = RPGState.COMBAT
    session.combat_state = CombatState()

    await channel.send("⚔️ **Combat Initiated!** Determining participants...", silent=True)

    participant_prompt = (
        "A combat encounter has begun. Based on the story so far, identify all potential participants besides the player character. "
        "From this list, choose ONE to be the 'Boss' and up to THREE others to be 'Mooks'. Any remaining characters are 'Bystanders'. "
        "The 'Boss' should be the most significant or threatening character currently present. 'Mooks' are lesser threats."
        "You MUST respond in a single JSON object with three keys: 'boss', 'mooks', and 'bystanders'. "
        "'boss' should be a single JSON object with 'name' and 'description' keys. "
        "'mooks' should be a LIST of objects, each with 'name' and 'description'. 'bystanders' should be a LIST of names."
        "If there are no suitable characters for a category, provide an empty value (null for boss, empty list for mooks/bystanders)."
        "\nExample: {\"boss\": {\"name\": \"Goblin King\", \"description\": \"A large, ugly goblin wearing a makeshift crown\"}, \"mooks\": [{\"name\": \"Goblin Archer\", \"description\": \"A scrawny goblin with a shortbow\"}], \"bystanders\": [\"Scared Villager\"]}"
    )
    
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})
    
    llm_payload = plot_context + session.story + [{"role": "system", "content": participant_prompt}]
    participant_json = await get_llm_json_response(client, session, llm_payload)

    if not participant_json:
        await channel.send("⚠️ Failed to determine combat participants. Aborting combat.", silent=True)
        session.state = RPGState.IDLE
        return

    if boss_data := participant_json.get("boss"):
        base_stats = _generate_npc_stats()
        boss_stats = {stat: val + 1 for stat, val in base_stats.items()}
        combat_stats = _calculate_combat_stats(boss_stats)
        combat_stats.hit_points = max(-8, math.floor(boss_stats.get("STR", 0) + boss_stats.get("CON", 0) / 2)) * 3
        combat_stats.magic_points = max(-8, math.floor(boss_stats.get("WIS", 0) + boss_stats.get("INT", 0) / 2)) * 3

        participant = CombatParticipant(
            name=boss_data.get("name", "Unknown Boss"),
            description=boss_data.get("description", "A mysterious figure."),
            distance=random.choice(DISTANCE_LEVELS),
            is_boss=True,
            stats=boss_stats,
            combat_stats=combat_stats
        )
        session.combat_state.participants.append(participant)

    if mook_data_list := participant_json.get("mooks"):
        for mook_data in mook_data_list[:3]:
            mook_stats = _generate_npc_stats()
            combat_stats = _calculate_combat_stats(mook_stats)
            combat_stats.hit_points = max(-8, math.floor(mook_stats.get("STR", 0) + mook_stats.get("CON", 0) / 2))
            combat_stats.magic_points = max(-8, math.floor(mook_stats.get("WIS", 0) + mook_stats.get("INT", 0) / 2))

            participant = CombatParticipant(
                name=mook_data.get("name", "Unknown Mook"),
                description=mook_data.get("description", "A generic foe."),
                distance=random.choice(DISTANCE_LEVELS),
                is_boss=False,
                stats=mook_stats,
                combat_stats=combat_stats
            )
            session.combat_state.participants.append(participant)

    if bystanders := participant_json.get("bystanders"):
        session.combat_state.bystanders = bystanders

    if not session.combat_state.participants:
        await channel.send("The air was tense, but no one seems to be attacking. The moment passes.", silent=True)
        session.state = RPGState.IDLE
        return

    embed = discord.Embed(
        title=f"Turn {session.combat_state.turn} - Player's Action", 
        description="You are up! Choose a target to interact with.",
        color=EMBED_COLOR_RPG
    )
    for p in session.combat_state.participants:
        role = "Boss" if p.is_boss else "Mook"
        stats_str = f"HP: {p.combat_stats.hit_points} | MP: {p.combat_stats.magic_points}"
        embed.add_field(
            name=f"[{role}] {p.name}",
            value=f"*{p.description}*\n**Distance:** {p.distance.title()}\n`{stats_str}`",
            inline=False
        )
    if session.combat_state.bystanders:
        embed.set_footer(text=f"Bystanders: {', '.join(session.combat_state.bystanders)}")
    
    await channel.send(embed=embed, view=PlayerCombatTurnView(session))


async def _begin_adventure(channel: discord.TextChannel, session: RPGSession, client: AsyncOpenAI, model: str):
    session.state = RPGState.IDLE
    session.combat_stats = _calculate_combat_stats(session.stats)
    _apply_gear_bonuses(session)

    await channel.send(content="*The threads of fate are weaving a secret destiny for you...*", silent=True)

    character_context = f"The player's character is described as follows: '{session.story[-1]['content']}'" if any(p['role'] == 'system' and 'Player description' in p['content'] for p in session.story) else "The player has not provided a character description."
    plot_generation_prompt = (
        "You are the creative force behind a role-playing adventure. "
        "Generate a cohesive and compelling story outline tailored to the player's character. "
        f"{character_context}\n"
        "Your response MUST be a single JSON object with the following keys: "
        "'PRIMARY_ALLY': A brief description of a character who will help the player. "
        "'PRIMARY_ANTAGONIST': A brief description of the main villain or opposing force. "
        "'SATISFYING_CONCLUSION': A brief description of the intended final outcome of the story. "
        "'OVERALL_PLOT': A JSON object containing the key stages of the adventure. It must have these exact keys: "
        "'FORESHADOWING': A subtle hint of the main conflict or antagonist. "
        "'INTRODUCTION': A scenario for how the player might meet the ally and antagonist. "
        "'CONFLICT': The core problem or struggle the player must face. "
        "'DEFEAT': A point where the player is expected to face a major setback. "
        "'REDEMPTION': An opportunity for the player to recover, grow, or find new strength after their defeat. "
        "'VICTORY': The final confrontation and resolution. "
        "Ensure the entire output is a single, valid JSON object and nothing else."
    )
    plot_payload = [{"role": "system", "content": plot_generation_prompt}]
    plot_json = await get_llm_json_response(client, session, plot_payload)

    if plot_json:
        session.plot_outline = plot_json
        logging.info(f"Generated plot outline for session in channel {channel.id}")
    else:
        logging.error(f"Failed to generate plot outline for session in channel {channel.id}")
        await channel.send("⚠️ Failed to generate the story's fate. The adventure will be purely improvised.")

    if session.combat_stats:
        base_stats_str = ' | '.join(f'{s}: {v:+}' for s, v in session.stats.items())
        cs = session.combat_stats
        combat_stats_str = (
            f"HP: {cs.hit_points} | MP: {cs.magic_points} | "
            f"Melee Atk: {cs.melee_attack:+} | Ranged Atk: {cs.ranged_attack:+} | Grapple Atk: {cs.grapple_attack:+} | "
            f"Magic Atk: {cs.magic_attack:+} | Miracle Atk: {cs.miracle_attack:+} | "
            f"Phys Def: {cs.physical_defense:+} | Magic Def: {cs.magic_defense:+} | "
            f"Initiative: {cs.initiative:+}"
        )
        for msg in session.story:
            if msg["role"] == "system" and "character stats" in msg["content"]:
                msg["content"] = f"The player's character stats are: {base_stats_str} // Combat Stats: {combat_stats_str}"
                break
    
    initial_story_message = await channel.send(f"The adventure is about to begin...")
    
    dungeon_master_prompt = "You are the Dungeon Master. Describe an immersive opening scene for the player. Introduce the environment and any NPCs. **Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
    
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

    llm_payload = plot_context + session.story + [{"role": "system", "content": dungeon_master_prompt}]
    llm_payload = _add_dm_personality_to_payload(session, llm_payload)
    
    await narrate_rpg_turn(channel, session, llm_payload, client, initial_story_message)

async def _start_gear_generation(channel: discord.TextChannel, session: RPGSession, client: AsyncOpenAI, model: str):
    while True: 
        session.inventory.clear()
        
        gear_embed = discord.Embed(
            title="🛠️ Let's Gear Up!",
            description="It's time to choose your equipment. We'll go through a list of item types one by one.",
            color=EMBED_COLOR_INCOMPLETE
        )
        gear_message = await channel.send(embed=gear_embed)

        for item_type, details in GEAR_CATALOG.items():
            confirm_view = ConfirmItemView(session.user_id)
            gear_embed.description = f"**Next up: {item_type}**\n*_{details['desc']}_*\n\nDo you want to have a **{item_type}**?"
            await gear_message.edit(embed=gear_embed, view=confirm_view)
            
            await confirm_view.wait() 

            interaction = confirm_view.interaction
            
            if confirm_view.choice:
                description_text = None
                modal = GearDescriptionModal(item_type)
                
                await interaction.response.send_modal(modal)
                await modal.wait() 

                if modal.description:
                    description_text = modal.description
                else:
                    await gear_message.edit(content="Timed out waiting for a description. Moving on...", embed=None, view=None)
                    continue

                target_stat = details['target']
                special_effect = None
                
                if item_type == "Special Trinket":
                    special_effect = await _get_llm_trinket_effect(client, model, description_text)

                if item_type == "Special Move":
                    move_target_view = SpecialMoveTargetView(session.user_id)
                    move_embed = discord.Embed(title="🎯 Choose a Target", description=f"Your special move, '{description_text}', needs to enhance one of your abilities. Which stat will it improve?", color=EMBED_COLOR_INCOMPLETE)
                    await gear_message.edit(embed=move_embed, view=move_target_view)
                    await move_target_view.wait()
                    if move_target_view.target_stat:
                        target_stat = move_target_view.target_stat
                    else: 
                        continue

                quality_view = ItemQualityView(session.user_id)
                quality_embed = discord.Embed(title="✨ Choose its Quality", description=f"How powerful is your **{item_type}**?\n*'{description_text}'*", color=EMBED_COLOR_INCOMPLETE)
                await gear_message.edit(embed=quality_embed, view=quality_view)
                await quality_view.wait()

                if quality_view.quality:
                    item = GearItem(
                        item_type=item_type,
                        description=description_text,
                        quality=quality_view.quality,
                        bonus=quality_view.bonus,
                        target_stat=target_stat,
                        special_effect=special_effect
                    )
                    session.inventory.append(item)
            else:
                pass
        
        inventory_embed = discord.Embed(title=f"{session.user_mention}'s Starting Gear", color=EMBED_COLOR_COMPLETE)
        if not session.inventory:
            inventory_embed.description = "You have chosen to venture forth with no starting gear. A bold choice!"
        else:
            for item in session.inventory:
                bonus_str = f"{item.bonus:+}"
                target_name = item.target_stat.replace('_', ' ').title()
                field_value = f"**Quality:** {item.quality} (`{bonus_str}` to **{target_name}**)\n*Description: {item.description}*"
                if item.special_effect:
                    field_value += f"\n**Effect:** *{item.special_effect}*"
                inventory_embed.add_field(name=f"🔹 {item.item_type}", value=field_value, inline=False)
        
        inventory_embed.set_footer(text="Do you want to keep this gear and begin your adventure, or start over?")
        finalize_view = FinalizeInventoryView(session.user_id)
        await gear_message.edit(embed=inventory_embed, view=finalize_view)
        await finalize_view.wait()

        if finalize_view.choice:
            await gear_message.edit(content="**Gear confirmed!**", embed=inventory_embed, view=None)
            break 
    return

class GearDescriptionModal(discord.ui.Modal, title="Describe Your Item"):
    description_input = discord.ui.TextInput(
        label="Name and Description",
        style=discord.TextStyle.paragraph,
        placeholder="e.g., The Sun Blade\nA golden sword that hums with a faint warmth.",
        required=True,
        min_length=5,
        max_length=250,
    )

    def __init__(self, item_type: str):
        super().__init__(timeout=300)
        self.title = f"✍️ Describe your {item_type}"
        self.description = None

    async def on_submit(self, interaction: discord.Interaction):
        self.description = self.description_input.value
        await interaction.response.defer()
        self.stop() 
        
        
class ConfirmDMPersonalityView(discord.ui.View):
    def __init__(self, session: 'RPGSession'):
        super().__init__(timeout=300)
        self.session = session
        self.choice_made = asyncio.Event()

    async def _handle_choice(self, interaction: discord.Interaction, use_custom_personality: bool):
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("⚠️ This is not your choice to make!", ephemeral=True)
            return

        for item in self.children:
            item.disabled = True
        
        if use_custom_personality:
            self.session.dm_personality = system_prompt 
            await interaction.response.edit_message(content="✅ The Dungeon Master's personality has been customized.", view=self)
        else:
            await interaction.response.edit_message(content="✅ The default Dungeon Master personality will be used.", view=self)
        
        self.choice_made.set()
        self.stop()

    @discord.ui.button(label="Yes", style=discord.ButtonStyle.success)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._handle_choice(interaction, True)

    @discord.ui.button(label="No", style=discord.ButtonStyle.danger)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._handle_choice(interaction, False)

class ConfirmItemView(discord.ui.View):
    def __init__(self, user_id: int):
        super().__init__(timeout=300)
        self.user_id = user_id
        self.choice = None
        self.interaction: Optional[discord.Interaction] = None 

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your choice to make!", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Yes, I want one.", style=discord.ButtonStyle.success)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = True
        self.interaction = interaction 
        self.stop()

    @discord.ui.button(label="No, I'll pass.", style=discord.ButtonStyle.danger)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = False
        self.interaction = interaction 
        await interaction.response.defer() 
        self.stop()

class ItemQualityView(discord.ui.View):
    def __init__(self, user_id: int):
        super().__init__(timeout=300)
        self.user_id = user_id
        self.quality = None
        self.bonus = None

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your choice to make!", ephemeral=True)
            return False
        return True
    
    async def set_quality(self, interaction: discord.Interaction, quality: str, bonus: int):
        self.quality = quality
        self.bonus = bonus
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()

    @discord.ui.button(label="Junky (-1)", style=discord.ButtonStyle.secondary, custom_id="junky")
    async def junky(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.set_quality(interaction, "Junky", -1)

    @discord.ui.button(label="Decent (+0)", style=discord.ButtonStyle.secondary, custom_id="decent")
    async def decent(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.set_quality(interaction, "Decent", 0)

    @discord.ui.button(label="Good (+1)", style=discord.ButtonStyle.primary, custom_id="good")
    async def good(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.set_quality(interaction, "Good", 1)

    @discord.ui.button(label="Legendary (+3)", style=discord.ButtonStyle.success, custom_id="legendary")
    async def legendary(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self.set_quality(interaction, "Legendary", 3)


class SpecialMoveTargetView(discord.ui.View):
    def __init__(self, user_id: int):
        super().__init__(timeout=300)
        self.user_id = user_id
        self.target_stat = None

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your choice to make!", ephemeral=True)
            return False
        return True

    async def set_target(self, interaction: discord.Interaction, stat: str):
        self.target_stat = stat
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()

    @discord.ui.button(label="Melee Attack", style=discord.ButtonStyle.primary, row=0)
    async def melee(self, i: discord.Interaction, b: discord.ui.Button): await self.set_target(i, "melee_attack")
    
    @discord.ui.button(label="Ranged Attack", style=discord.ButtonStyle.primary, row=0)
    async def ranged(self, i: discord.Interaction, b: discord.ui.Button): await self.set_target(i, "ranged_attack")

    @discord.ui.button(label="Grapple Attack", style=discord.ButtonStyle.primary, row=0)
    async def grapple(self, i: discord.Interaction, b: discord.ui.Button): await self.set_target(i, "grapple_attack")

    @discord.ui.button(label="Magic Attack", style=discord.ButtonStyle.primary, row=1)
    async def magic(self, i: discord.Interaction, b: discord.ui.Button): await self.set_target(i, "magic_attack")
    
    @discord.ui.button(label="Miracle Attack", style=discord.ButtonStyle.primary, row=1)
    async def miracle(self, i: discord.Interaction, b: discord.ui.Button): await self.set_target(i, "miracle_attack")

    @discord.ui.button(label="Physical Defense", style=discord.ButtonStyle.secondary, row=2)
    async def phys_def(self, i: discord.Interaction, b: discord.ui.Button): await self.set_target(i, "physical_defense")

    @discord.ui.button(label="Magical Defense", style=discord.ButtonStyle.secondary, row=2)
    async def mag_def(self, i: discord.Interaction, b: discord.ui.Button): await self.set_target(i, "magic_defense")


class FinalizeInventoryView(discord.ui.View):
    def __init__(self, user_id: int):
        super().__init__(timeout=600)
        self.user_id = user_id
        self.choice = None

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your decision!", ephemeral=True)
            return False
        return True

    @discord.ui.button(label="Keep This Gear", style=discord.ButtonStyle.success)
    async def keep(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = True
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()

    @discord.ui.button(label="Discard and Start Over", style=discord.ButtonStyle.danger)
    async def discard(self, interaction: discord.Interaction, button: discord.ui.Button):
        self.choice = False
        for item in self.children:
            item.disabled = True
        await interaction.response.edit_message(view=self)
        self.stop()
        
class ConfirmCombatModuleView(discord.ui.View):
    def __init__(self, session: 'RPGSession'):
        super().__init__(timeout=300)
        self.session = session
        self.choice_made = asyncio.Event()

    async def _handle_choice(self, interaction: discord.Interaction, enabled: bool):
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("This is not your choice to make!", ephemeral=True)
            return

        self.session.combat_module_enabled = enabled
        for item in self.children:
            item.disabled = True

        if enabled:
            message = "✅ **Combat Module Activated.** Actions will now be evaluated for combat."
        else:
            message = "✅ **Combat Module Deactivated.** The adventure will proceed with pure roleplaying."
        
        await interaction.response.edit_message(content=message, view=self)
        self.choice_made.set()
        self.stop()

    @discord.ui.button(label="Yes, Activate", style=discord.ButtonStyle.success)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._handle_choice(interaction, True)

    @discord.ui.button(label="No, Keep it Narrative", style=discord.ButtonStyle.danger)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._handle_choice(interaction, False)
        
class RPGActionView(ui.View):
    def __init__(self, session: RPGSession, trivial_actions: List[str]):
        super().__init__(timeout=None)
        self.session = session
        
        for i, stat_name in enumerate(STAT_NAMES):
            stat_value = session.stats.get(stat_name, 0)
            button_label = f"{stat_name} {stat_value:+}"
            
            button = ui.Button(
                label=button_label,
                style=discord.ButtonStyle.secondary,
                custom_id=f"rpg_stat_{stat_name}",
                row=i // 3
            )
            button.callback = self.on_stat_button_click
            self.add_item(button)
            
        for i, action in enumerate(trivial_actions[:3]):
            button_row = 2 + i
            if button_row > 4:
                break
            
            button = ui.Button(
                label=action[:80],
                style=discord.ButtonStyle.primary,
                custom_id=f"rpg_action_{i}",
                row=button_row
            )
            button.callback = self.on_trivial_action_click
            self.add_item(button)

    async def on_stat_button_click(self, interaction: discord.Interaction):
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("⚠️ This is not your adventure!", ephemeral=True)
            return
        stat = interaction.data["custom_id"].split("_")[-1]
        self.session.state = RPGState.AWAITING_STAT_ACTION_INPUT
        self.session.pending_stat_for_action = stat
        await interaction.response.send_message(f"❓ How would you like to use your **{stat}**? (Reply to the DM's last message to describe your action)", ephemeral=True)

    async def on_trivial_action_click(self, interaction: discord.Interaction):
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("⚠️ This is not your adventure!", ephemeral=True)
            return
        await interaction.response.defer()
        for item in self.children: item.disabled = True
        await interaction.message.edit(view=self)
        
        action_index = int(interaction.data["custom_id"].split('_')[-1])
        action_buttons = [item for item in self.children if isinstance(item, ui.Button) and item.custom_id and item.custom_id.startswith("rpg_action_")]
        button_label = action_buttons[action_index].label if 0 <= action_index < len(action_buttons) else ""
        
        dice = await _roll_dice(2)
        if not dice or len(dice) < 2:
            await interaction.followup.send("❌ Error rolling dice for trivial action.", ephemeral=True)
            return
            
        d1, d2 = dice[0], dice[1]
        raw_roll = d1 - d2
        
        interim_roll = raw_roll - 1 if raw_roll > 0 else raw_roll
        final_value = max(1, interim_roll)

        roll_summary = (f"**Trivial Action:** *{button_label}*\n"
                        f"**Roll:** `[{d1} - {d2}] = {raw_roll}` → **Result Value: {final_value}** (from 1-4)")

        self.session.story.append({"role": "user", "content": f"I will {button_label}"})
        
        outcome_prompt = (
            "This was a trivial action that has consequences. "
            f"The player tried to: '{button_label}'. "
            f"The action's success level is {final_value} on a scale of 1 to 4. "
            "Narrate the CONSEQUENCES of this result, advancing the plot. A '1' is a minor success, maybe with a small, unexpected twist. A '4' is a surprisingly effective success. "
            "The previous challenge should be resolved, creating a new situation. "
            "**Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
        )

        provider, model = curr_model.split("/", 1)
        openai_client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

        plot_context = []
        if self.session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(self.session.plot_outline)}"})

        llm_payload = plot_context + self.session.story + [{"role": "system", "content": outcome_prompt}]
        llm_payload = _add_dm_personality_to_payload(self.session, llm_payload) 
        await narrate_rpg_turn(interaction.channel, self.session, llm_payload, openai_client, interaction.message, roll_details_text=roll_summary)

def _calculate_combat_stats(stats: Dict[str, int]) -> 'CombatStats':
    str_ = stats.get("STR", 0)
    dex_ = stats.get("DEX", 0)
    con_ = stats.get("CON", 0)
    int_ = stats.get("INT", 0)
    wis_ = stats.get("WIS", 0)
    cha_ = stats.get("CHA", 0)

    initiative = math.floor(dex_ + int_ / 2)
    hp_base = math.floor(str_ + con_ / 2)
    mp_base = math.floor(wis_ + int_ / 2)
    melee_attack = math.floor(str_ + dex_ / 2)
    ranged_attack = math.floor(wis_ + dex_ / 2)
    magic_attack = math.floor(int_ + cha_ / 2)
    miracle_attack = math.floor(wis_ + cha_ / 2)
    grapple_attack = math.floor(str_ + con_ / 2) 
    physical_defense = math.floor(con_ + dex_ / 2)
    magic_defense = math.floor(int_ + wis_ / 2)

    return CombatStats(
        initiative=max(-8, initiative),
        hit_points=max(-8, hp_base) * 3,
        magic_points=max(-8, mp_base) * 3,
        melee_attack=max(-8, melee_attack),
        ranged_attack=max(-8, ranged_attack),
        magic_attack=max(-8, magic_attack),
        miracle_attack=max(-8, miracle_attack),
        grapple_attack=max(-8, grapple_attack), 
        physical_defense=max(-8, physical_defense),
        magic_defense=max(-8, magic_defense)
    )
    
async def get_llm_json_response(client: AsyncOpenAI, session: 'RPGSession', payload: list, retries=3) -> Any:
    vanilla_payload = _add_dm_personality_to_payload(session, payload, force_vanilla=True)
    
    for _ in range(retries):
        try:
            response = await client.chat.completions.create(
                model=curr_model.split('/', 1)[1], 
                messages=vanilla_payload, 
                stream=False, 
                response_format={"type": "json_object"}
            )
            raw_content = response.choices[0].message.content
            
            try:
                return json.loads(raw_content)
            except json.JSONDecodeError:
                match = re.search(r'```(json)?\s*(\{.*\})\s*```', raw_content, re.DOTALL)
                if match:
                    try:
                        return json.loads(match.group(2))
                    except json.JSONDecodeError:
                        logging.warning(f"Found JSON in markdown, but failed to parse: {match.group(2)}")
                        continue 
                
                logging.warning(f"Failed to decode JSON directly, will retry. Content: {raw_content}")
                await asyncio.sleep(1)

        except Exception as e:
            logging.error(f"Error getting JSON from LLM: {e}. Retrying...")
            await asyncio.sleep(1)
    return None

async def narrate_rpg_turn(channel: discord.TextChannel, session: RPGSession, llm_payload: list, client: AsyncOpenAI, message_to_reply: discord.Message, roll_details_text: str = "", event_notification: Optional[str] = None):
    try:
        embed = discord.Embed(description=STREAMING_INDICATOR, color=EMBED_COLOR_INCOMPLETE)
        response_msg = await message_to_reply.reply(embed=embed, silent=True)
        narrative = await stream_llm_response(channel, response_msg, llm_payload, client)
        session.story.append({"role": "assistant", "content": narrative})
        
        trivial_actions_prompt = "Based on the last scene description, suggest three distinct, simple, one-sentence actions a player could take. These actions should be trivial and not require a skill check. Please ensure that you use fewer than 8 words for these options. Respond *only* with a valid JSON object containing a single key 'actions' with a list of 1-3 strings. Example: {\"actions\": [\"Look under the bed.\", \"Open the window.\", \"Listen at the door.\"]}"
        
        plot_context = []
        if session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})
        
        actions_payload = plot_context + session.story + [{"role": "user", "content": trivial_actions_prompt}]
        actions_json = await get_llm_json_response(client, session, actions_payload)
        trivial_actions = actions_json.get("actions", []) if isinstance(actions_json, dict) else []
        
        narrative_with_event = narrative
        if event_notification:
            narrative_with_event = f"{narrative}\n\n**{event_notification}**"

        final_description = f"{narrative_with_event}\n\n{roll_details_text}" if roll_details_text else narrative_with_event

        final_embed = discord.Embed(description=final_description, color=EMBED_COLOR_RPG)
        
        await response_msg.edit(embed=final_embed, view=RPGActionView(session, trivial_actions))
        session.state = RPGState.IDLE
        session.pending_action_text = session.pending_stat_for_action = session.pending_cv = session.pending_dv = session.pending_fv = session.pending_fv_details = None
    except Exception as e:
        logging.exception("Error during RPG narration turn.")
        await channel.send(f"❌ A critical error occurred during the DM's narration: {e}")

rpg_group = app_commands.Group(name="rpg", description="Commands for the RPG system.")

async def _roll_dice(num_dice: int) -> Optional[List[int]]:
    try:
        url = f"https://www.random.org/integers/?num={num_dice}&min=1&max=6&col=1&base=10&format=plain&rnd=new"
        async with aiohttp.ClientSession() as http_session:
            async with http_session.get(url) as resp:
                resp.raise_for_status()
                text = await resp.text()
                return [int(n) for n in text.splitlines() if n]
    except Exception as e:
        logging.error(f"Could not fetch dice rolls from random.org, using fallback: {e}")
        return [random.randint(1, 6) for _ in range(num_dice)]

async def _roll_erratic_value() -> int:
    try:
        url = "https://www.random.org/integers/?num=4&min=1&max=6&col=1&base=10&format=plain&rnd=new"
        async with aiohttp.ClientSession() as http_session:
            async with http_session.get(url) as resp:
                resp.raise_for_status()
                text = await resp.text()
                dice = [int(n) for n in text.splitlines() if n]
    except Exception:
        logging.warning("Could not fetch dice from random.org for EV, using fallback.")
        dice = [random.randint(1, 6) for _ in range(4)]
    
    return (dice[0] + dice[1]) - (dice[2] + dice[3])


class CustomizeStatView(discord.ui.View):
    def __init__(self, original_interaction: discord.Interaction, stat_name: str, dice: List[int], parent_view: 'StatGenerationView'):
        super().__init__(timeout=300)
        self.original_interaction = original_interaction
        self.stat_name = stat_name
        self.dice = dice
        self.parent_view = parent_view
        self._update_dice_buttons()

    def _update_dice_buttons(self):
        self.clear_items()
        for i, value in enumerate(self.dice):
            button = discord.ui.Button(label=f"{value:+}", style=discord.ButtonStyle.primary if value > 0 else discord.ButtonStyle.secondary, custom_id=f"flip_{i}")
            button.callback = self.flip_button_callback
            self.add_item(button)
        finish_button = discord.ui.Button(label="Finish", style=discord.ButtonStyle.success, custom_id="finish_customize")
        finish_button.callback = self.finish_button_callback
        self.add_item(finish_button)

    async def flip_button_callback(self, interaction: discord.Interaction):
        index_to_flip = int(interaction.data['custom_id'].split('_')[1])
        self.dice[index_to_flip] *= -1
        new_total = sum(self.dice)
        self._update_dice_buttons()
        await interaction.response.edit_message(
            content=f"Customizing **{self.stat_name} = {new_total:+}**. Click buttons to flip signs.", 
            view=self
        )

    async def finish_button_callback(self, interaction: discord.Interaction):
        if sum(1 for d in self.dice if d > 0) == 2 and sum(1 for d in self.dice if d < 0) == 2:
            self.parent_view.stats[self.stat_name] = sum(self.dice)
            self.parent_view.current_stat_index += 1
            await self.parent_view.show_next_stat(interaction)
        else:
            await interaction.response.send_message("You must have exactly two positive and two negative dice.", ephemeral=True)

class StatGenerationView(discord.ui.View):
    def __init__(self, *, original_interaction: discord.Interaction):
        super().__init__(timeout=300)
        self.original_interaction = original_interaction
        self.stats: Dict[str, int] = {}
        self.current_stat_index = 0
        self.final_stats: Optional[Dict[str, int]] = None

    async def start(self):
        await self.show_next_stat(self.original_interaction)

    async def show_next_stat(self, interaction: discord.Interaction):
        if self.current_stat_index < len(STAT_NAMES):
            stat_name = STAT_NAMES[self.current_stat_index]
            dice = await _roll_dice(4)
            if not dice:
                await self.original_interaction.edit_original_response(content="❌ Could not get dice rolls. Please try again.", view=None)
                self.stop()
                return

            signs = [1, 1, -1, -1]
            random.shuffle(signs)
            initial_signed_dice = [d * s for d, s in zip(dice, signs)]
            stat_value = sum(initial_signed_dice)
            self.stats[stat_name] = stat_value
            
            dice_str = ', '.join(map(str, dice))
            signed_dice_str = ", ".join(f"{d:+}" for d in initial_signed_dice)
            message = (
                f"Rolling for **{stat_name}**...\n"
                f"Dice Rolled: `{dice_str}`\n"
                f"Random Initial Assignment: `[{signed_dice_str}]`\n"
                f"**Initial Total: {stat_value:+}**\n\n"
                "What would you like to do?"
            )

            view = discord.ui.View(timeout=300)
            async def keep_callback(inner_interaction: discord.Interaction):
                self.current_stat_index += 1
                await self.show_next_stat(inner_interaction)
            async def customize_callback(inner_interaction: discord.Interaction):
                initial_total = sum(initial_signed_dice)
                customize_view = CustomizeStatView(self.original_interaction, stat_name, initial_signed_dice, self)
                await inner_interaction.response.edit_message(
                    content=f"Customizing **{stat_name} = {initial_total:+}**. Click buttons to flip signs.", 
                    view=customize_view
                )

            keep_button = discord.ui.Button(label="Keep", style=discord.ButtonStyle.success)
            keep_button.callback = keep_callback
            
            customize_button = discord.ui.Button(label="Customize", style=discord.ButtonStyle.primary)
            customize_button.callback = customize_callback
            
            view.add_item(keep_button)
            view.add_item(customize_button)
            
            if interaction.type == discord.InteractionType.application_command:
                await interaction.edit_original_response(content=message, view=view)
            else:
                await interaction.response.edit_message(content=message, view=view)
        else:
            await self.show_final_summary(interaction)
            
    async def show_final_summary(self, interaction: discord.Interaction):
        stats_display = "\n".join(f"**{stat}**: {val:+}" for stat, val in self.stats.items())
        message = f"All stats generated for {self.original_interaction.user.mention}!\n{stats_display}"
        view = discord.ui.View(timeout=300)

        async def finalize_callback(inner_interaction: discord.Interaction):
            for item in view.children: item.disabled = True
            final_message = f"**Stats Confirmed** for {self.original_interaction.user.mention}!\n{stats_display}"
            await inner_interaction.response.edit_message(content=final_message, view=view)
            self.final_stats = self.stats
            self.stop()
        async def reroll_callback(inner_interaction: discord.Interaction):
            self.current_stat_index = 0
            self.stats = {}
            await self.show_next_stat(inner_interaction)

        finalize_button = discord.ui.Button(label="Finalize", style=discord.ButtonStyle.success)
        finalize_button.callback = finalize_callback
        
        reroll_button = discord.ui.Button(label="Reroll All", style=discord.ButtonStyle.danger)
        reroll_button.callback = reroll_callback

        view.add_item(finalize_button)
        view.add_item(reroll_button)
        await interaction.response.edit_message(content=message, view=view)

    async def on_timeout(self):
        await self.original_interaction.edit_original_response(content="❌ Character roll timed out.", view=None)

async def _start_rpg_session(interaction: discord.Interaction, stats: Dict[str, int]):
    user = interaction.user
    session = RPGSession(user_id=user.id, user_mention=user.mention, stats=stats, story=[
        {"role": "system", "content": "You are a Dungeon Master for a one-shot RPG adventure."},
        {"role": "system", "content": f"The player's character stats are: { ' | '.join(f'{s}: {v:+}' for s, v in stats.items()) }"}
    ])
    rpg_sessions[interaction.channel_id] = session
    session.state = RPGState.AWAITING_DESCRIPTION
    
    send_method = interaction.followup.send if interaction.response.is_done() else interaction.channel.send

    prompt_message = (f"**Your character is ready, {user.mention}!**\n\n"
                    "Before we begin, would you like to provide a brief description of your character? "
                    "This could be their name, appearance, or a bit of their backstory.\n\n"
                    "**Please reply to this message with your description.** (Or reply with `skip` if you'd rather not.)")
    await send_method(prompt_message)
    
@rpg_group.command(name="rollchar", description="Create a character with randomly generated stats.")
@is_authorized()
async def rpg_rollchar(interaction: discord.Interaction):
    if interaction.channel_id in rpg_sessions:
        await interaction.response.send_message("⚠️ An RPG session is already active in this channel.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    view = StatGenerationView(original_interaction=interaction)
    await view.start()
    await view.wait()

    if view.final_stats:
        await interaction.followup.send("Character roll complete. The adventure begins in the channel!", ephemeral=True)
        await _start_rpg_session(interaction, view.final_stats)
        
@rpg_group.command(name="createchar", description="Create a character by assigning your own stats.")
@is_authorized()
async def rpg_createchar(
    interaction: discord.Interaction,
    strength: app_commands.Range[int, -8, 8],
    dexterity: app_commands.Range[int, -8, 8],
    constitution: app_commands.Range[int, -8, 8],
    intelligence: app_commands.Range[int, -8, 8],
    wisdom: app_commands.Range[int, -8, 8],
    charisma: app_commands.Range[int, -8, 8],
):
    if interaction.channel_id in rpg_sessions:
        await interaction.response.send_message("⚠️ An RPG session is already active in this channel.", ephemeral=True)
        return

    await interaction.response.defer()

    stats = {
        "STR": strength, "DEX": dexterity, "CON": constitution,
        "INT": intelligence, "WIS": wisdom, "CHA": charisma
    }

    stats_display = "\n".join(f"**{stat}**: {val:+}" for stat, val in stats.items())
    message_content = (
        f"You have assigned the following stats for your character, {interaction.user.mention}:\n{stats_display}\n\n"
        "Would you like to keep this character and begin the adventure?"
    )

    class ConfirmCharacterView(discord.ui.View):
        def __init__(self):
            super().__init__(timeout=300)
            self.confirmed = False

        @discord.ui.button(label="Keep Character", style=discord.ButtonStyle.success)
        async def keep(self, button_interaction: discord.Interaction, button: discord.ui.Button):
            if button_interaction.user.id != interaction.user.id:
                await button_interaction.response.send_message("⚠️ This is not your character to confirm.", ephemeral=True)
                return

            self.confirmed = True
            for item in self.children:
                item.disabled = True
            await button_interaction.response.edit_message(
                content=f"**Stats Confirmed** for {interaction.user.mention}!\n{stats_display}",
                view=self
            )
            self.stop()

        @discord.ui.button(label="Discard", style=discord.ButtonStyle.danger)
        async def discard(self, button_interaction: discord.Interaction, button: discord.ui.Button):
            if button_interaction.user.id != interaction.user.id:
                await button_interaction.response.send_message("⚠️ This is not your character to discard.", ephemeral=True)
                return
            
            for item in self.children:
                item.disabled = True
            await button_interaction.response.edit_message(content="Character discarded.", view=self)
            self.stop()

    view = ConfirmCharacterView()
    await interaction.followup.send(message_content, view=view)
    await view.wait()

    if view.confirmed:
        await _start_rpg_session(interaction, stats)

class RollDiceView(discord.ui.View):
    def __init__(self, session: RPGSession):
        super().__init__(timeout=180) 
        self.session = session
        self.message: Optional[discord.Message] = None

        self.roll_button = discord.ui.Button(
            label=f"Roll for {session.pending_stat_for_action} vs DV {session.pending_dv}",
            style=discord.ButtonStyle.primary,
            custom_id="rpg_roll_dice"
        )
        self.roll_button.callback = self.roll_button_callback
        self.add_item(self.roll_button)

    async def roll_button_callback(self, interaction: discord.Interaction):
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("⚠️ It's not your turn to roll.", ephemeral=True)
            return
        
        self.roll_button.disabled = True
        await interaction.response.edit_message(view=self)

        dice_rolls = await _roll_dice(8)
        if not dice_rolls or len(dice_rolls) < 8:
            await interaction.followup.send("❌ Error rolling dice. Please try again.", ephemeral=True)
            return
        
        pos, neg = sum(dice_rolls[:4]), sum(dice_rolls[4:])
        stat_bonus = self.session.stats[self.session.pending_stat_for_action]
        
        fv_bonus = self.session.pending_fv or 0
        fv_details = self.session.pending_fv_details or "None"
        
        final_result = (pos - neg) + stat_bonus + fv_bonus
        dv, cv = self.session.pending_dv, self.session.pending_cv
        margin = final_result - dv
        
        outcomes = {7: "Amazing success", 5: "Great success", 3: "OK success", 1: "Slight success", 
                    -1: "Slight failure", -3: "Kinda bad failure", -5: "Bad failure", -999: "Terrible failure"}
        outcome_desc = next(v for k, v in sorted(outcomes.items(), reverse=True) if margin >= k)

        roll_summary = (f"**Action:** *{self.session.pending_action_text}*\n"
                        f"**Check:** {self.session.pending_stat_for_action} `({stat_bonus:+})` vs **DV** `{dv}` (CV: `{cv:+}` | FV: `{fv_bonus:+}`)\n"
                        f"**FV Details:** *{fv_details}*\n"
                        f"**Roll:** `[{pos} - {neg}]` (Roll) `+ {stat_bonus}` (Stat) `+ {fv_bonus}` (FV) `=` **{final_result}**\n"
                        f"**Result:** **{final_result}** vs **DV {dv}** | **Margin:** `{margin:+}` | **Outcome:** {outcome_desc}")

        provider, model = curr_model.split("/", 1)
        client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

        # --- FIX STARTS HERE ---
        # Add the action and its outcome to a temporary context to check if combat should start NOW.
        combat_check_context = [
            {"role": "user", "content": self.session.pending_action_text},
            {"role": "system", "content": f"The result of that action was: {outcome_desc} (Margin: {margin:+})"}
        ]
        combat_needed = await _check_if_combat_is_needed(client, model, self.session, self.session.pending_action_text, extra_context=combat_check_context)

        if combat_needed and self.session.combat_module_enabled:
            # The action has led to combat. Add it to the story and initialize combat.
            self.session.story.append({"role": "user", "content": self.session.pending_action_text})
            self.session.story.append({"role": "system", "content": f"The action resulted in combat starting. Roll details: {roll_summary}"})
            await interaction.message.edit(content=f"The situation escalates! Your action has initiated combat!\n\n{roll_summary}", view=None)
            await _initialize_combat(interaction.channel, self.session, client, model)
            return
        # --- FIX ENDS HERE ---

        self.session.story.append({"role": "user", "content": self.session.pending_action_text})

        if outcome_desc == "Terrible failure":
            death_check_prompt = (
                f"The player attempted to '{self.session.pending_action_text}' and the result was a 'Terrible failure' ({roll_summary}). "
                "In the context of the story and this specific failure, does this event directly result in the character's death? "
                "The death should be a plausible and immediate consequence of the failed action. "
                "Respond with a single word: YES or NO."
            )
            plot_context = [{"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(self.session.plot_outline)}"} if self.session.plot_outline else {"role": "system", "content": "No plot outline provided."}]
            death_payload = plot_context + self.session.story + [{"role": "system", "content": death_check_prompt}]
            
            response = await client.chat.completions.create(model=model, messages=death_payload, stream=False, temperature=0)
            death_result = response.choices[0].message.content.strip().upper()

            if "YES" in death_result:
                await interaction.message.edit(content=f"**FATAL FAILURE**\n{roll_summary}", view=None)
                
                reason_for_death = (
                    f"The character has died. The final action was attempting to '{self.session.pending_action_text}', "
                    f"which resulted in a terrible, fatal failure ({outcome_desc})."
                )
                await _conclude_rpg_session(interaction.channel, self.session, reason_for_death)
                return

        outcome_prompt = (
            "This was a pivotal moment. The action CANNOT be repeated. The outcome is now a permanent part of the story. "
            f"The player tried to: '{self.session.pending_action_text}'. "
            f"The definitive result of this irreversible action was: '{outcome_desc}'. "
            "Narrate the CONSEQUENCES of this result. Do not describe the attempt; describe what HAPPENS NOW. "
            "Crucially, the situation has fundamentally changed. The previous challenge is now resolved (either passed or failed, creating a new problem). "
            "**Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
        )
        
        plot_context = []
        if self.session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(self.session.plot_outline)}"})

        llm_payload = plot_context + self.session.story + [{"role": "system", "content": outcome_prompt}]
        llm_payload = _add_dm_personality_to_payload(self.session, llm_payload) 

        
        narration_starter_msg = await interaction.channel.send(content="*Dice hit the table...*")
        
        await narrate_rpg_turn(interaction.channel, self.session, llm_payload, client, narration_starter_msg, roll_details_text=roll_summary)
        
        await interaction.message.edit(content=f"Roll processed for action: *{self.session.pending_action_text}*", view=None)


    async def on_timeout(self):
        self.roll_button.disabled = True
        await self.message.edit(content="Roll timed out.", view=self)


async def _conclude_rpg_session(channel: discord.TextChannel, session: RPGSession, conclusion_reason: str):
    await channel.send(f"**The adventure concludes...**")
    
    conclusion_prompt = (
        f"The adventure is now over. {conclusion_reason}. "
        "Based on the story so far, provide a concluding narrative, wrapping up the adventure with a brief but satisfying end. "
        "Describe the final state of the world and the legacy (or lack thereof) of the character's actions."
    )

    provider, model = curr_model.split("/", 1)
    client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))
    
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

    llm_payload = plot_context + session.story + [{"role": "user", "content": conclusion_prompt}]
    llm_payload = _add_dm_personality_to_payload(session, llm_payload) 

    
    reply_target = channel.last_message or await channel.send("...")

    try:
        await stream_llm_response(channel, reply_target, llm_payload, client)
    except Exception as e:
        logging.error(f"Error during RPG conclusion: {e}")
        await channel.send(f"❌ An error occurred during the final narration: {e}")
    finally:
        if channel.id in rpg_sessions:
            del rpg_sessions[channel.id]
            
            
@rpg_group.command(name="conclude", description="Ends the current RPG session.")
@is_authorized()
async def rpg_conclude(interaction: discord.Interaction):
    session = rpg_sessions.get(interaction.channel_id)
    if not session or interaction.user.id != session.user_id:
        await interaction.response.send_message("⚠️ No active session for you to conclude here.", ephemeral=True)
        return
    
    await interaction.response.send_message("✅ Manually concluding the RPG session.", ephemeral=True)
    
    reason = "The player has chosen to end the session."
    await _conclude_rpg_session(interaction.channel, session, reason)
        
discord_bot.tree.add_command(rpg_group)

async def _get_llm_binary_evaluation(client: AsyncOpenAI, model: str, action_text: str, eval_type: str) -> bool:
    prompt_templates = {
        "creativity": "You are an evaluator of player actions in a role-playing game. Your sole purpose is to determine if an action is creative. 'Creative' means it is imaginative, clever, or not a straightforward, predictable choice. Respond with only a single word: YES or NO.\n\nPlayer action: '{action}'",
        "uniqueness": "You are an evaluator of player actions in a role-playing game. Your sole purpose is to determine if an action is unique. 'Unique' means it avoids common fantasy tropes and is not an action that is tried constantly by players (e.g., 'I attack the monster', 'I look for traps'). Respond with only a single word: YES or NO.\n\nPlayer action: '{action}'"
    }
    if eval_type not in prompt_templates:
        return False
        
    prompt = prompt_templates[eval_type].format(action=action_text)
    
    try:
        payload = [{"role": "system", "content": prompt}]
        response = await client.chat.completions.create(model=model, messages=payload, stream=False, temperature=0, max_tokens=5)
        result = response.choices[0].message.content.strip().upper()
        return "YES" in result
    except Exception as e:
        logging.error(f"Error during LLM binary evaluation for {eval_type}: {e}")
        return False

async def _continue_adventure_setup(channel: discord.TextChannel, session: RPGSession, description_provided: bool):
    combat_view = ConfirmCombatModuleView(session)
    await channel.send(
        "Before your adventure begins, do you want to **activate the combat module?**\n\n"
        "If you select **Yes**, your actions will be evaluated for potential combat encounters which will be handled by a dedicated system. "
        "If you select **No**, all situations will be resolved through pure narrative roleplaying.",
        view=combat_view
    )
    await combat_view.choice_made.wait()

    provider, model = curr_model.split("/", 1)
    client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

    if session.combat_module_enabled:
        await _start_gear_generation(channel, session, client, model)

    await _begin_adventure(channel, session, client, model)

    
@discord_bot.event
async def on_message(new_msg: discord.Message):
    if new_msg.author.bot:
        return

    session = rpg_sessions.get(new_msg.channel.id)
    
    if not session or session.state == RPGState.SETUP or session.state == RPGState.COMBAT:
        return

    is_player = new_msg.author.id == session.user_id
    is_reply_to_bot = new_msg.reference and new_msg.reference.resolved and new_msg.reference.resolved.author == discord_bot.user

    if not (is_player and is_reply_to_bot):
        return

    if session.state == RPGState.AWAITING_DESCRIPTION:
        await new_msg.reference.resolved.delete()
        
        description_provided = False
        if new_msg.content.strip().lower() not in ['no', 'n', 'skip']:
            description_text = new_msg.content
            session.story.append({"role": "system", "content": f"Player description: \"{description_text}\""})
            description_provided = True
        
        await new_msg.delete()

        personality_view = ConfirmDMPersonalityView(session)
        prompt_msg = (
            f"**Your character is taking shape!**\n\n"
            f"The default Dungeon Master has a specific personality defined in `system_prompt`. "
            f"Would you like to use this custom personality for your adventure?"
        )
        await new_msg.channel.send(prompt_msg, view=personality_view)
        
        await personality_view.choice_made.wait()

        session.state = RPGState.SETUP 
        
        await _continue_adventure_setup(new_msg.channel, session, description_provided)
        return

    elif session.state in [RPGState.IDLE, RPGState.AWAITING_STAT_ACTION_INPUT]:
        action_text = new_msg.content
        session.pending_action_text = action_text
        
        provider, model = curr_model.split("/", 1)
        client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))
        
        try:
            view = discord.ui.View.from_message(new_msg.reference.resolved)
            if view:
                for item in view.children: item.disabled = True
                await new_msg.reference.resolved.edit(view=view)
        except Exception as e:
            logging.warning(f"Could not disable buttons: {e}")
        await new_msg.delete()

        # --- FIX STARTS HERE ---
        # Temporarily add the user's action to the context for the check, without modifying the main story yet.
        combat_check_context = [{"role": "user", "content": action_text}]
        combat_needed = await _check_if_combat_is_needed(client, model, session, action_text, extra_context=combat_check_context)
        # --- FIX ENDS HERE ---

        if combat_needed and session.combat_module_enabled:
            session.story.append({"role": "user", "content": action_text}) # Now add it to the story
            await _initialize_combat(new_msg.channel, session, client, model)
            return
        
        additional_context = []
        if combat_needed and not session.combat_module_enabled:
            additional_context.append({
                "role": "system",
                "content": "SYSTEM NOTE: The player's action just triggered a situation that would normally lead to combat, but the combat module is disabled. You must resolve this tense, dangerous moment using the standard narrative and dice roll system instead of a turn-based fight."
            })

        fv_bonus = 0
        fv_details_parts = []
        word_count = len(action_text.split())
        if word_count > 20:
            fv_bonus += 2
            fv_details_parts.append(f"Wordy ({word_count} words): +2")
        elif word_count < 10:
            fv_bonus -= 2
            fv_details_parts.append(f"Brief ({word_count} words): -2")
        
        is_creative = await _get_llm_binary_evaluation(client, model, action_text, "creativity")
        if is_creative:
            fv_bonus += 2
            fv_details_parts.append("Creative: +2")

        is_unique = await _get_llm_binary_evaluation(client, model, action_text, "uniqueness")
        if is_unique:
            fv_bonus += 2
            fv_details_parts.append("Unique: +2")

        session.pending_fv = fv_bonus
        session.pending_fv_details = ", ".join(fv_details_parts) if fv_details_parts else "None"

        ev = await _roll_erratic_value()
        if ev < -6 or ev > 6:
            session.story.append({"role": "user", "content": action_text})
            plot_context = [{"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"} if session.plot_outline else {"role": "system", "content": "No plot outline."}]
            
            erratic_event_prompt = (
                f"An 'ERRATIC EVENT' has been triggered (EV: {ev})! The player just tried to: '{action_text}'. You MUST now narrate a COMPLETELY UNEXPECTED and wild turn of events. This event should be related to the player's action and the overall story, but it must throw the narrative off balance. It can be good, bad, or bizarre, but it must be a major narrative twist. Describe this shocking development. **Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
            )
            payload = plot_context + session.story + additional_context + [{"role": "system", "content": erratic_event_prompt}]
            payload = _add_dm_personality_to_payload(session, payload)
            await narrate_rpg_turn(new_msg.channel, session, payload, client, new_msg.reference.resolved, event_notification=f"ERRATIC EVENT!! (EV: {ev:+})")
            return

        session.story.append({"role": "user", "content": action_text})
        plot_context = [{"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"} if session.plot_outline else {"role": "system", "content": "No plot outline."}]

        cv_prompt = (
            f"A player wants to: '{action_text}'. Analyze this action's potential to fundamentally change the current situation or "
            "advance the narrative. Is this a minor, descriptive interaction, or a pivotal, plot-driving moment? "
            "A 'trivial' action (CV between -2 and 2) will be narrated as a simple success and will not change the core challenge. "
            "A 'critical' action (CV outside -2 and 2) represents an attempt to overcome a real obstacle and MUST change the state of the story. "
            "Based on this, respond with a JSON object with one key 'cv' and an integer from -7 (trivial) to +7 (story-altering). "
            "Example: {\"cv\": 5}"
        )
        cv_payload = plot_context + session.story + additional_context + [{"role": "system", "content": cv_prompt}]
        cv_json = await get_llm_json_response(client, session, cv_payload) 
        cv = cv_json.get("cv", 0) if cv_json else 0
        session.pending_cv = cv

        if -2 <= cv <= 2:
            success_prompt = (
                f"The player's action, '{action_text}', is a simple one that succeeds without needing a roll. "
                "Narrate this successful outcome. It should be a brief, descriptive event that does not significantly alter the plot. "
                "**Your response must NOT offer the player a list of choices or suggested actions.** "
                "Conclude your narrative with only the open-ended question, 'What do you do now?'"
            )
            payload = plot_context + session.story + additional_context + [{"role": "system", "content": success_prompt}]
            payload = _add_dm_personality_to_payload(session, payload)
            await narrate_rpg_turn(new_msg.channel, session, payload, client, new_msg.reference.resolved)
        else:
            instruction_template = (
                "Evaluate the following player action: '{action_text}'.\n\n"
                "Your task is to determine the most logical character stat (STR, DEX, CON, INT, WIS, CHA) to use for this action, and its intrinsic difficulty. "
                "You MUST IGNORE the player's character, their stats, their backstory, and all previous events. "
                "Your assessment must be based SOLELY on how difficult the action would be for a normal, average human with all stats at +0.\n\n"
                "First, choose the most appropriate stat. Second, determine a base Difficulty Value (DV) for this action on a scale from -7 (trivial for a normal person) to +7 (nearly impossible for a normal person).\n\n"
                "Respond ONLY with the stat and the DV, separated by a comma. Example: 'DEX,3'"
            )
            
            if session.state == RPGState.AWAITING_STAT_ACTION_INPUT:
                stat_to_use = session.pending_stat_for_action
                stat_prompt = (
                    f"Evaluate the following player action: '{action_text}' (using the {stat_to_use} stat).\n\n"
                    "Your task is to determine the intrinsic difficulty of this action. "
                    "You MUST IGNORE the player's character, their stats, their backstory, and all previous events. "
                    "Your assessment must be based SOLELY on how difficult the action would be for a normal, average human with all stats at +0.\n\n"
                    f"The player is using {stat_to_use}. Determine a base Difficulty Value (DV) for this action on a scale from -7 (trivial for a normal person) to +7 (nearly impossible for a normal person).\n\n"
                    f"Respond ONLY with '{stat_to_use}' and the DV, separated by a comma. Example: '{stat_to_use},3'"
                )
            else:
                stat_prompt = instruction_template.format(action_text=action_text)
            
            stat_payload = plot_context + session.story + additional_context + [{"role": "system", "content": stat_prompt}]
            stat_response = await client.chat.completions.create(model=model, messages=stat_payload, stream=False)
            raw_response = stat_response.choices[0].message.content.strip()
            match = re.search(r'([A-Z]{3}),\s*(-?\d+)', raw_response)

            if match:
                stat, dv_str = match.groups()
                final_dv = int(dv_str) + (cv // 2 if abs(cv) >= 5 else 0)
                session.pending_stat_for_action, session.pending_dv, session.state = stat.upper(), final_dv, RPGState.AWAITING_ROLL
                criticality_text = "**CRITICAL ACTION**" if abs(cv) >= 5 else "Action"
                
                view = RollDiceView(session)
                message_content = f"{session.user_mention}, {criticality_text} requires a roll.\n> *{action_text}*"
                sent_message = await new_msg.channel.send(message_content, view=view)
                view.message = sent_message
            else:
                await new_msg.channel.send(f"I couldn't determine the check for your action (got: `{raw_response}`). Please rephrase and reply to my last message.")
                session.story.pop()
                session.state = RPGState.IDLE
        return
        
async def stream_llm_response(channel: discord.TextChannel, initial_message: discord.Message, llm_payload: list[dict[str, Any]], openai_client: AsyncOpenAI, user_warnings: set[str] = set()) -> str:
    global last_task_time
    full_response_content = ""
    response_msg = initial_message
    edit_task = None
    max_len = 4096 - len(STREAMING_INDICATOR)
    embed = discord.Embed(description=STREAMING_INDICATOR, color=EMBED_COLOR_INCOMPLETE)
    if user_warnings:
        embed.title = " ".join(user_warnings)
    await response_msg.edit(embed=embed, view=None)

    try:
        provider, model = curr_model.split("/", 1)
        params = config["models"].get(curr_model, {})
        stream = await openai_client.chat.completions.create(model=model, messages=llm_payload, stream=True, **params)
        async for chunk in stream:
            if delta := (chunk.choices[0].delta.content or ""):
                full_response_content += delta
            if (edit_task is None or edit_task.done()) and (datetime.now().timestamp() - last_task_time >= EDIT_DELAY_SECONDS):
                if edit_task: await edit_task
                display_content = full_response_content
                if len(display_content) > max_len:
                    display_content = display_content[:max_len] + "..."
                embed.description = display_content + STREAMING_INDICATOR
                edit_task = asyncio.create_task(response_msg.edit(embed=embed))
                last_task_time = datetime.now().timestamp()
        if edit_task: await edit_task
        embed.description = full_response_content
        embed.color = EMBED_COLOR_RPG
        await response_msg.edit(embed=embed)
    except Exception as e:
        logging.exception("Error streaming LLM response")
        embed.description = f"❌ An error occurred: {e}"
        await response_msg.edit(embed=embed)
    return full_response_content
    
@discord_bot.event
async def on_ready():
    logging.info(f'Logged in as {discord_bot.user} (ID: {discord_bot.user.id})')
    if client_id := config.get("client_id"):
        logging.info(f"BOT INVITE URL: https://discord.com/oauth2/authorize?client_id={client_id}&permissions=412317273088&scope=bot")
    await discord_bot.tree.sync()

async def main():
    token = config.get("bot_token")
    if not token:
        logging.critical("Bot token not found in config.yaml. Please add it.")
        return
    await discord_bot.start(token)

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logging.info("Bot shutting down.")