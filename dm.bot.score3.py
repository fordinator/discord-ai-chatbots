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
    """Holds all derived combat statistics for a character."""
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
    """Represents a single item in the player's inventory."""
    item_type: str
    description: str
    quality: str
    bonus: int
    target_stat: Optional[str] = None
    special_effect: Optional[str] = None

class RPGState(Enum):
    IDLE = auto()
    AWAITING_ROLL = auto()
    AWAITING_STAT_ACTION_INPUT = auto()
    AWAITING_DESCRIPTION = auto()

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
    overall_goal: Optional[str] = None
    turn_limit: Optional[int] = None
    current_turn: int = 0
    roll_margins: List[int] = field(default_factory=list)
    high_fv_actions_count: int = 0
    antagonist_is_dead: bool = False
    player_is_dead: bool = False

def _add_dm_personality_to_payload(session: 'RPGSession', payload: list[dict[str, Any]], force_vanilla: bool = False) -> list[dict[str, Any]]:
    if session.dm_personality and not force_vanilla:
        personality_prompt = {"role": "system", "content": session.dm_personality}
        return [personality_prompt] + payload
    return payload
    
async def _check_if_combat_is_needed(client: AsyncOpenAI, model: str, session: RPGSession, action_text: str) -> bool:
    prompt = (
        "Based on the story so far and the player's latest action, does this action necessitate the start of a "
        "turn-based combat encounter? The story should only proceed to combat if it is an unavoidable and direct "
        f"consequence of this action: '{action_text}'. Respond with only a single word: YES or NO."
    )
    
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

    payload = plot_context + session.story + [{"role": "system", "content": prompt}]
    
    try:
        response = await client.chat.completions.create(model=model, messages=payload, stream=False, temperature=0, max_tokens=5)
        result = response.choices[0].message.content.strip().upper()
        return "YES" in result
    except Exception as e:
        logging.error(f"Error during LLM combat check: {e}")
        return False
        
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
    if not session.combat_stats: 
        session.combat_stats = _calculate_combat_stats(session.stats)

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

class SetTurnLimitView(discord.ui.View):
    def __init__(self, session: 'RPGSession'):
        super().__init__(timeout=300)
        self.session = session
        self.choice_made = asyncio.Event()

    async def set_limit(self, interaction: discord.Interaction, limit: Optional[int]):
        if interaction.user.id != self.session.user_id:
            await interaction.response.send_message("This is not your choice to make!", ephemeral=True)
            return
        
        self.session.turn_limit = limit
        for item in self.children:
            item.disabled = True
            
        if limit:
            message = f"✅ **Turn Limit Set to {limit}.** If you exceed this limit, your final score will be penalized."
        else:
            message = "✅ **No Turn Limit Set.** Play as long as you wish, but your score will be penalized for sessions longer than 7 turns."
            
        await interaction.response.edit_message(content=message, view=self)
        self.choice_made.set()
        self.stop()

    @discord.ui.button(label="10 Turns", style=discord.ButtonStyle.primary, row=0)
    async def ten_turns(self, i: discord.Interaction, b: discord.ui.Button): await self.set_limit(i, 10)
    
    @discord.ui.button(label="15 Turns", style=discord.ButtonStyle.primary, row=0)
    async def fifteen_turns(self, i: discord.Interaction, b: discord.ui.Button): await self.set_limit(i, 15)

    @discord.ui.button(label="25 Turns", style=discord.ButtonStyle.primary, row=0)
    async def twenty_five_turns(self, i: discord.Interaction, b: discord.ui.Button): await self.set_limit(i, 25)

    @discord.ui.button(label="No Limit", style=discord.ButtonStyle.secondary, row=1)
    async def no_limit(self, i: discord.Interaction, b: discord.ui.Button): await self.set_limit(i, None)

# --- REFACTORED: This new function handles the final part of the setup ---
async def _finalize_rpg_setup(channel: discord.TextChannel, session: RPGSession, client: AsyncOpenAI, model: str):
    """Generates plot, goal, turn limit and starts the adventure. Called for both combat and narrative paths."""
    await channel.send(content="*The threads of fate are weaving a secret destiny for you...*", silent=True)

    character_desc = next((p['content'] for p in session.story if 'Player description' in p.get('content', '')), "The player has not provided a character description.")

    plot_generation_prompt = (
        "You are the creative force behind a role-playing adventure. "
        f"Generate a cohesive and compelling story outline tailored to the player's character: '{character_desc}'\n"
        "Your response MUST be a single JSON object with the following keys: "
        "'PRIMARY_ALLY', 'PRIMARY_ANTAGONIST', 'SATISFYING_CONCLUSION', and an 'OVERALL_PLOT' object with keys "
        "'FORESHADOWING', 'INTRODUCTION', 'CONFLICT', 'DEFEAT', 'REDEMPTION', 'VICTORY'. "
        "Ensure the entire output is a single, valid JSON object and nothing else."
    )
    plot_payload = [{"role": "system", "content": plot_generation_prompt}]
    plot_json = await get_llm_json_response(client, session, plot_payload)

    if plot_json:
        session.plot_outline = plot_json
        logging.info(f"Generated plot outline for session in channel {channel.id}")

        goal_prompt_text = (
            f"Based on the player's character ('{character_desc}') and the primary antagonist ('{plot_json.get('PRIMARY_ANTAGONIST', 'Unknown')}'), "
            "create a one or two-sentence overall goal for the player's adventure. This goal must involve surviving and actively frustrating the antagonist's plans. "
            "Respond ONLY with the text of the goal itself."
        )
        goal_payload = [{"role": "system", "content": goal_prompt_text}]
        try:
            goal_response = await client.chat.completions.create(model=model, messages=goal_payload, stream=False, temperature=0.7, max_tokens=100)
            overall_goal = goal_response.choices[0].message.content.strip()
            session.overall_goal = overall_goal
            session.plot_outline['OVERALL_GOAL'] = overall_goal
        except Exception as e:
            logging.error(f"Failed to generate overall goal: {e}")
            session.overall_goal = f"Survive and defeat the {plot_json.get('PRIMARY_ANTAGONIST', 'hidden foe')}."
        
        goal_embed = discord.Embed(title="🎯 Your Destiny is Forged", description=f"**Your Goal:** {session.overall_goal}", color=EMBED_COLOR_RPG)
        await channel.send(embed=goal_embed)
    else:
        logging.error(f"Failed to generate plot outline for session in channel {channel.id}")
        await channel.send("⚠️ Failed to generate the story's fate. The adventure will be purely improvised.")

    turn_limit_view = SetTurnLimitView(session)
    await channel.send(
        "How long do you have to achieve this destiny? You can set a turn limit for your adventure.",
        view=turn_limit_view
    )
    await turn_limit_view.choice_made.wait()

    if not session.combat_stats:
        session.combat_stats = _calculate_combat_stats(session.stats)
    
    _apply_gear_bonuses(session) # Apply gear bonuses (will be none if skipped)

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
    """The main controller for the entire gear generation process. This no longer starts the game."""
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

            if confirm_view.choice:
                description_prompt_embed = discord.Embed(
                    title=f"✍️ Describe your {item_type}",
                    description=f"Excellent! **Please reply to this message** with a name and a brief description for your {item_type}.",
                    color=EMBED_COLOR_INCOMPLETE
                )
                await gear_message.edit(embed=description_prompt_embed, view=None)

                try:
                    description_msg: discord.Message = await discord_bot.wait_for(
                        'message',
                        timeout=300.0,
                        check=lambda m: m.author.id == session.user_id and m.reference and m.reference.message_id == gear_message.id
                    )
                    description_text = description_msg.content
                    await description_msg.delete()
                except asyncio.TimeoutError:
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
            break

    await gear_message.edit(content="**Gear confirmed!** Preparing the adventure...", embed=inventory_embed, view=None)

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

# --- FIXED: This view now properly acknowledges interactions ---
class ConfirmItemView(discord.ui.View):
    def __init__(self, user_id: int):
        super().__init__(timeout=300)
        self.user_id = user_id
        self.choice: Optional[bool] = None

    async def interaction_check(self, interaction: discord.Interaction) -> bool:
        if interaction.user.id != self.user_id:
            await interaction.response.send_message("This is not your choice to make!", ephemeral=True)
            return False
        return True

    async def _handle_response(self, interaction: discord.Interaction, choice: bool):
        """Helper to disable buttons and acknowledge the interaction."""
        self.choice = choice
        for item in self.children:
            item.disabled = True
        # This edit acknowledges the interaction so Discord doesn't mark it as "failed"
        await interaction.response.edit_message(view=self)
        self.stop()

    @discord.ui.button(label="Yes, I want one.", style=discord.ButtonStyle.success)
    async def yes(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._handle_response(interaction, True)

    @discord.ui.button(label="No, I'll pass.", style=discord.ButtonStyle.danger)
    async def no(self, interaction: discord.Interaction, button: discord.ui.Button):
        await self._handle_response(interaction, False)

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
        
        self.session.current_turn += 1

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
        try:
            response_msg = await message_to_reply.reply(embed=embed, silent=True)
        except discord.NotFound: 
            response_msg = await channel.send(embed=embed)

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
            narrative_with_event = f"**{event_notification}**\n\n{narrative}"

        final_description = f"{narrative_with_event}\n\n{roll_details_text}" if roll_details_text else narrative_with_event
        
        if session.current_turn > 0:
            turn_limit_str = f" / {session.turn_limit}" if session.turn_limit else ""
            final_description = f"**TURN {session.current_turn:02}{turn_limit_str}**\n\n{final_description}"

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
    session = RPGSession(
        user_id=user.id, 
        user_mention=user.mention, 
        stats=stats, 
        story=[
            {"role": "system", "content": "You are a Dungeon Master for a one-shot RPG adventure."},
            {"role": "system", "content": f"The player's character stats are: { ' | '.join(f'{s}: {v:+}' for s, v in stats.items()) }"}
        ]
    )
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
        
        self.session.current_turn += 1

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
        
        self.session.roll_margins.append(margin)

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
                
                self.session.player_is_dead = True
                reason_for_death = (
                    f"The character died while attempting to '{self.session.pending_action_text}', "
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

async def _calculate_and_display_final_score(channel: discord.TextChannel, session: RPGSession, client: AsyncOpenAI, model: str, conclusion_reason: str):
    await channel.send("`Analyzing adventure records and calculating final score...`")
    
    base_score = 0
    base_score_reason = ""
    
    if session.player_is_dead:
        base_score = 0
        base_score_reason = "Character was killed in action."
    else:
        antagonist = session.plot_outline.get('PRIMARY_ANTAGONIST', 'the antagonist') if session.plot_outline else 'the antagonist'
        antagonist_check_prompt = (
            f"Please analyze the complete story text provided. Based *only* on the events in this text, is the primary antagonist, '{antagonist}', unequivocally dead or permanently defeated by the end of the story? Respond with only a single word: YES or NO."
        )
        story_text = "\n".join([f"{msg['role']}: {msg['content']}" for msg in session.story])
        antagonist_payload = [{"role": "system", "content": antagonist_check_prompt}, {"role": "user", "content": story_text}]
        
        try:
            response = await client.chat.completions.create(model=model, messages=antagonist_payload, stream=False, temperature=0, max_tokens=5)
            result = response.choices[0].message.content.strip().upper()
            if "YES" in result:
                session.antagonist_is_dead = True
                base_score = 100
                base_score_reason = "Primary Antagonist was defeated."
        except Exception as e:
            logging.error(f"Error during antagonist death check: {e}")

        if not session.antagonist_is_dead:
            goal_eval_prompt = (
                "You are a neutral evaluator. You will be given a story goal and the full text of an RPG session. Your task is to provide a score from 0 to 100 based on how well the player accomplished the stated goal. Do not add any commentary or explanation. "
                f"THE GOAL: '{session.overall_goal}'.\n\n"
                "THE STORY:\n"
                f"{story_text}\n\n"
                "Based on the story, how well was the goal accomplished? Respond ONLY with a single integer between 0 and 100."
            )
            goal_payload = [{"role": "system", "content": goal_eval_prompt}]
            try:
                response = await client.chat.completions.create(model=model, messages=goal_payload, stream=False, temperature=0.2, max_tokens=10)
                base_score = int(re.search(r'\d+', response.choices[0].message.content).group())
                base_score_reason = "Based on narrative accomplishment of the goal."
            except (Exception, AttributeError) as e:
                logging.error(f"Error during goal evaluation, defaulting score: {e}")
                base_score = 50 
                base_score_reason = "Based on narrative accomplishment (defaulted due to error)."

    score = base_score
    
    fv_bonus = session.high_fv_actions_count
    score += fv_bonus
    
    margin_bonus = sum(session.roll_margins)
    score += margin_bonus

    stat_adjustment = 0
    for stat_val in session.stats.values():
        stat_adjustment -= stat_val
    score += stat_adjustment
    
    subtotal = max(0, min(100, score))

    final_score = subtotal
    turn_diff = session.current_turn - 7
    multiplier = 0
    if turn_diff > 0: 
        multiplier = -0.10 * turn_diff
    elif turn_diff < 0: 
        multiplier = -0.10 * turn_diff 
        
    final_score = int(max(0, min(100, final_score)))

    embed = discord.Embed(title="Adventure Complete: Final Score", color=EMBED_COLOR_COMPLETE)
    embed.description = f"**Character:** {session.user_mention}\n**Conclusion:** {conclusion_reason}"
    
    embed.add_field(name="🏆 Base Score", value=f"`{base_score}` _({base_score_reason})_", inline=False)
    embed.add_field(name="✨ Fancy Value Bonus", value=f"`{fv_bonus:+}` _({session.high_fv_actions_count} actions with FV ≥ +6)_", inline=False)
    embed.add_field(name="🎲 Margin of Success Bonus", value=f"`{margin_bonus:+}` _(Sum of all roll margins)_", inline=False)
    embed.add_field(name="🧠 Stat Adjustment", value=f"`{stat_adjustment:+}` _(Bonus for low stats, penalty for high stats)_", inline=False)
    embed.add_field(name="📊 Subtotal", value=f"**`{subtotal} / 100`**", inline=False)
    embed.add_field(name="⏳ Turn-Based Multiplier", value=f"`{multiplier:.0%}` _({session.current_turn} turns vs. a baseline of 7)_", inline=False)
    embed.add_field(name="⭐ Final Score", value=f"**`{final_score} / 100`**", inline=False)
    
    await channel.send(embed=embed)

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

    try:
        reply_target = await channel.fetch_message(channel.last_message_id)
    except (discord.NotFound, discord.HTTPException):
        reply_target = await channel.send("...")

    try:
        await stream_llm_response(channel, reply_target, llm_payload, client)
    except Exception as e:
        logging.error(f"Error during RPG conclusion: {e}")
        await channel.send(f"❌ An error occurred during the final narration: {e}")
    finally:
        await _calculate_and_display_final_score(channel, session, client, model, conclusion_reason)
        
        if channel.id in rpg_sessions:
            del rpg_sessions[channel.id]
            
@rpg_group.command(name="conclude", description="Ends the current RPG session and calculates your score.")
@is_authorized()
async def rpg_conclude(interaction: discord.Interaction):
    session = rpg_sessions.get(interaction.channel_id)
    if not session or interaction.user.id != session.user_id:
        await interaction.response.send_message("⚠️ No active session for you to conclude here.", ephemeral=True)
        return
    
    await interaction.response.send_message("✅ Manually concluding the RPG session. Your final score will be calculated.", ephemeral=True)
    
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

# --- MODIFIED: This is now the main setup controller ---
async def _continue_adventure_setup(channel: discord.TextChannel, session: RPGSession, description_provided: bool):
    """Asks about combat module, then continues to the appropriate setup path."""
    combat_view = ConfirmCombatModuleView(session)
    await channel.send(
        "Before your adventure begins, do you want to **activate the combat module?**\n\n"
        "If you select **Yes**, your actions will be evaluated for potential combat encounters which will be handled by a dedicated system, and you will be able to select gear.\n\n"
        "If you select **No**, all situations will be resolved through pure narrative roleplaying and you will forgo starting equipment.",
        view=combat_view
    )
    await combat_view.choice_made.wait()

    provider, model = curr_model.split("/", 1)
    client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

    if session.combat_module_enabled:
        await _start_gear_generation(channel, session, client, model)
    else:
        await channel.send("`Your adventure will be a pure narrative experience. Forgoing gear, you step into the world...`")
    
    # This function is now called for both paths to finish setup and start the game.
    await _finalize_rpg_setup(channel, session, client, model)

@discord_bot.event
async def on_message(new_msg: discord.Message):
    if new_msg.author.bot:
        return

    session = rpg_sessions.get(new_msg.channel.id)
    if not session:
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

        combat_needed = await _check_if_combat_is_needed(client, model, session, action_text)

        if combat_needed and session.combat_module_enabled:
            await new_msg.channel.send("⚔️ **Combat Initiated!**\n*(The combat system will take over from here.)*")
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
        
        if fv_bonus >= 6:
            session.high_fv_actions_count += 1

        session.pending_fv = fv_bonus
        session.pending_fv_details = ", ".join(fv_details_parts) if fv_details_parts else "None"

        ev = await _roll_erratic_value()
        if ev < -6 or ev > 6:
            session.current_turn += 1 
            session.story.append({"role": "system", "content": action_text})
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
            session.current_turn += 1 
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