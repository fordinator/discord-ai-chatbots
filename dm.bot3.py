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

        # If no specific permissions are set in the config, allow the command.
        if not allowed_user_ids and not allowed_channel_ids:
            return True

        # Check if the user is on the allowed list, which grants access anywhere.
        if interaction.user.id in allowed_user_ids:
            return True

        # If not an allowed user, check for allowed channels (only applies in servers).
        if interaction.guild is not None and interaction.channel_id in allowed_channel_ids:
            return True
        
        # If none of the conditions are met, the check fails.
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
    plot_outline: Optional[Dict[str, Any]] = None # ADDED: For plot generation
    dm_personality: Optional[str] = None # ADD THIS LINE
    state: RPGState = RPGState.IDLE
    pending_action_text: Optional[str] = None
    pending_stat_for_action: Optional[str] = None
    pending_cv: Optional[int] = None
    pending_dv: Optional[int] = None
    # MODIFICATION: Added pending_fv fields to store Fancy Value bonus and details.
    pending_fv: Optional[int] = None
    pending_fv_details: Optional[str] = None

def _add_dm_personality_to_payload(session: 'RPGSession', payload: list[dict[str, Any]], force_vanilla: bool = False) -> list[dict[str, Any]]:
    """Prepends the custom DM personality to the LLM payload if it exists and is not forced to be vanilla."""
    if session.dm_personality and not force_vanilla:
        personality_prompt = {"role": "system", "content": session.dm_personality}
        # Ensure it's the very first message for context
        return [personality_prompt] + payload
    return payload
    
    
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
            self.session.dm_personality = system_prompt # Global system_prompt from config
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

    # MODIFICATION: This entire function is changed to handle the new trivial action roll.
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
        
        # 1. Roll 2d6 from RANDOM.ORG
        dice = await _roll_dice(2)
        if not dice or len(dice) < 2:
            await interaction.followup.send("❌ Error rolling dice for trivial action.", ephemeral=True)
            return
            
        d1, d2 = dice[0], dice[1]
        raw_roll = d1 - d2
        
        # 2. Calculate the final value based on the specified logic (1-4 range).
        # If the raw roll is positive, subtract 1. Then, take the maximum of that result and 1.
        # This maps the raw [-5, 5] range to the desired [1, 4] outcome range.
        interim_roll = raw_roll - 1 if raw_roll > 0 else raw_roll
        final_value = max(1, interim_roll)

        roll_summary = (f"**Trivial Action:** *{button_label}*\n"
                        f"**Roll:** `[{d1} - {d2}] = {raw_roll}` → **Result Value: {final_value}** (from 1-4)")

        self.session.story.append({"role": "user", "content": f"I will {button_label}"})
        
        # 3. Create a new prompt for the LLM that instructs it to advance the plot based on the roll.
        outcome_prompt = (
            "This was a trivial action that has consequences. "
            f"The player tried to: '{button_label}'. "
            f"The action's success level is {final_value} on a scale of 1 to 4. "
            "Narrate the CONSEQUENCES of this result, advancing the plot. A '1' is a minor success, maybe with a small, unexpected twist. A '4' is a surprisingly effective success. "
            "The previous challenge should be resolved, creating a new situation. "
            "**Your response MUST include fewer than 2,000 words.** "
            "**Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
        )

        provider, model = curr_model.split("/", 1)
        openai_client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

        plot_context = []
        if self.session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(self.session.plot_outline)}"})

        llm_payload = plot_context + self.session.story + [{"role": "system", "content": outcome_prompt}]
        llm_payload = _add_dm_personality_to_payload(self.session, llm_payload) # ADD THIS
        # 4. Call the narration function, passing the roll details to be displayed to the user.
        await narrate_rpg_turn(interaction.channel, self.session, llm_payload, openai_client, interaction.message, roll_details_text=roll_summary)

async def get_llm_json_response(client: AsyncOpenAI, session: 'RPGSession', payload: list, retries=3) -> Any:
    """
    Gets a JSON response from the LLM, optionally forcing the personality prompt to be excluded.
    It will also attempt to clean the response before parsing.
    """
    # Force vanilla payload to prevent personality bleed-through on JSON tasks
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
            
            # First attempt: parse directly
            try:
                return json.loads(raw_content)
            except json.JSONDecodeError:
                # Second attempt: find JSON within markdown code blocks
                match = re.search(r'```(json)?\s*(\{.*\})\s*```', raw_content, re.DOTALL)
                if match:
                    try:
                        return json.loads(match.group(2))
                    except json.JSONDecodeError:
                        logging.warning(f"Found JSON in markdown, but failed to parse: {match.group(2)}")
                        continue # Try again
                
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
        # MODIFICATION: Reset pending FV fields after a turn is fully narrated.
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
    """
    Rolls 2d6 - 2d6 for an Erratic Value (EV). Returns an integer between -10 and 10.
    """
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
    """
    Finalizes character stats, creates the RPG session, and prompts the user for a description.
    """
    user = interaction.user
    session = RPGSession(user_id=user.id, user_mention=user.mention, stats=stats, story=[
        {"role": "system", "content": "You are a Dungeon Master for a one-shot RPG adventure."},
        {"role": "system", "content": f"The player's character stats are: { ' | '.join(f'{s}: {v:+}' for s, v in stats.items()) }"}
    ])
    rpg_sessions[interaction.channel_id] = session
    session.state = RPGState.AWAITING_DESCRIPTION
    
    # Use followup.send for interactions that have been deferred or already responded to.
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
    """Allows a user to create a character by specifying their six stat values."""
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
        super().__init__(timeout=180)  # Set a timeout for the view
        self.session = session
        self.message: Optional[discord.Message] = None

        self.roll_button = discord.ui.Button(
            label=f"Roll for {session.pending_stat_for_action} vs DV {session.pending_dv}",
            style=discord.ButtonStyle.primary,
            custom_id="rpg_roll_dice"
        )
        self.roll_button.callback = self.roll_button_callback
        self.add_item(self.roll_button)

    # MODIFICATION: This function is updated to calculate and display the Fancy Value (FV).
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
        
        # 1. Retrieve the calculated Fancy Value from the session.
        fv_bonus = self.session.pending_fv or 0
        fv_details = self.session.pending_fv_details or "None"
        
        # 2. Add the FV to the final roll result.
        final_result = (pos - neg) + stat_bonus + fv_bonus
        dv, cv = self.session.pending_dv, self.session.pending_cv
        margin = final_result - dv
        
        outcomes = {7: "Amazing success", 5: "Great success", 3: "OK success", 1: "Slight success", 
                    -1: "Slight failure", -3: "Kinda bad failure", -5: "Bad failure", -999: "Terrible failure"}
        outcome_desc = next(v for k, v in sorted(outcomes.items(), reverse=True) if margin >= k)

        # 3. Create a more detailed roll summary that includes the FV breakdown.
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
            "**Your response MUST include fewer than 2,000 words.** "
            "**Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
        )
        
        plot_context = []
        if self.session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(self.session.plot_outline)}"})

        llm_payload = plot_context + self.session.story + [{"role": "system", "content": outcome_prompt}]
        llm_payload = _add_dm_personality_to_payload(self.session, llm_payload) # ADD THIS

        
        narration_starter_msg = await interaction.channel.send(content="*Dice hit the table...*")
        
        await narrate_rpg_turn(interaction.channel, self.session, llm_payload, client, narration_starter_msg, roll_details_text=roll_summary)
        
        await interaction.message.edit(content=f"Roll processed for action: *{self.session.pending_action_text}*", view=None)


    async def on_timeout(self):
        self.roll_button.disabled = True
        await self.message.edit(content="Roll timed out.", view=self)


async def _conclude_rpg_session(channel: discord.TextChannel, session: RPGSession, conclusion_reason: str):
    """
    Handles the logic for concluding an RPG session, narrating the end, and cleaning up.
    """
    await channel.send(f"**The adventure concludes...**")
    
    conclusion_prompt = (
        f"The adventure is now over. {conclusion_reason}. "
        "Based on the story so far, provide a concluding narrative, wrapping up the adventure with a brief but satisfying end. "
        "Describe the final state of the world and the legacy (or lack thereof) of the character's actions."
        "**Your response MUST include fewer than 2,000 words.** "
    )

    provider, model = curr_model.split("/", 1)
    client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))
    
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

    llm_payload = plot_context + session.story + [{"role": "user", "content": conclusion_prompt}]
    llm_payload = _add_dm_personality_to_payload(session, llm_payload) # ADD THIS

    
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

# MODIFICATION: New helper function to get a binary (YES/NO) evaluation from the LLM for FV calculation.
async def _get_llm_binary_evaluation(client: AsyncOpenAI, model: str, action_text: str, eval_type: str) -> bool:
    """Gets a simple YES/NO evaluation from the LLM for a given action in a fresh session."""
    prompt_templates = {
        "creativity": "You are an evaluator of player actions in a role-playing game. Your sole purpose is to determine if an action is creative. 'Creative' means it is imaginative, clever, or not a straightforward, predictable choice. Respond with only a single word: YES or NO.\n\nPlayer action: '{action}'",
        "uniqueness": "You are an evaluator of player actions in a role-playing game. Your sole purpose is to determine if an action is unique. 'Unique' means it avoids common fantasy tropes and is not an action that is tried constantly by players (e.g., 'I attack the monster', 'I look for traps'). Respond with only a single word: YES or NO.\n\nPlayer action: '{action}'"
    }
    if eval_type not in prompt_templates:
        return False
        
    prompt = prompt_templates[eval_type].format(action=action_text)
    
    try:
        # Per the request, use a fresh session with no history for this evaluation.
        payload = [{"role": "system", "content": prompt}]
        response = await client.chat.completions.create(model=model, messages=payload, stream=False, temperature=0, max_tokens=5)
        result = response.choices[0].message.content.strip().upper()
        return "YES" in result
    except Exception as e:
        logging.error(f"Error during LLM binary evaluation for {eval_type}: {e}")
        return False

async def _continue_adventure_setup(channel: discord.TextChannel, session: RPGSession, description_provided: bool):
    """Generates plot and starts the adventure after personality choice."""
    await channel.send(content="*The threads of fate are weaving a secret destiny for you...*", silent=True)

    provider, model = curr_model.split("/", 1)
    client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

    character_context = f"The player's character is described as follows: '{session.story[-1]['content']}'" if description_provided else "The player has not provided a character description."
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

    ack_msg = "Your character description has been recorded and your destiny set." if description_provided else "No description provided. A mysterious destiny has been set."
    initial_story_message = await channel.send(f"{ack_msg}\nThe adventure is about to begin...")
    
    dungeon_master_prompt = "You are the Dungeon Master. Describe an immersive opening scene for the player. Introduce the environment and any NPCs. **Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?' **Your response MUST include fewer than 2,000 words.**"
    
    # --- This is the key change for all subsequent calls ---
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

    llm_payload = plot_context + session.story + [{"role": "system", "content": dungeon_master_prompt}]
    llm_payload = _add_dm_personality_to_payload(session, llm_payload) # Use the helper
    
    await narrate_rpg_turn(channel, session, llm_payload, client, initial_story_message)
    
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

    # --- Start of Corrected Logic Block ---

    # STATE 1: Player is submitting their character description
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
        return # This return is now fine, as it's the end of this logical path.

    # STATE 2: Player is taking an action during the game
    elif session.state in [RPGState.IDLE, RPGState.AWAITING_STAT_ACTION_INPUT]:
        action_text = new_msg.content
        session.pending_action_text = action_text
        
        provider, model = curr_model.split("/", 1)
        client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))
        
        try:
            view = discord.ui.View.from_message(new_msg.reference.resolved)
            if view:
                for item in view.children:
                    item.disabled = True
                await new_msg.reference.resolved.edit(view=view)
        except Exception as e:
            logging.warning(f"Could not disable buttons: {e}")
        await new_msg.delete()
        
        # --- FV Calculation Block ---
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
        # --- END of FV Calculation ---

        ev = await _roll_erratic_value()
        if ev < -6 or ev > 6:
            session.story.append({"role": "system", "content": action_text})
            plot_context = []
            if session.plot_outline:
                plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})
            
            erratic_event_prompt = (
                f"An 'ERRATIC EVENT' has been triggered (EV: {ev})! The player just tried to: '{action_text}'. You MUST now narrate a COMPLETELY UNEXPECTED and wild turn of events. This event should be related to the player's action and the overall story, but it must throw the narrative off balance. It can be good, bad, or bizarre, but it must be a major narrative twist. Describe this shocking development. **Your response MUST include fewer than 2,000 words.** **Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
            )
            payload = plot_context + session.story + [{"role": "system", "content": erratic_event_prompt}]
            payload = _add_dm_personality_to_payload(session, payload)
            await narrate_rpg_turn(new_msg.channel, session, payload, client, new_msg.reference.resolved, event_notification=f"ERRATIC EVENT!! (EV: {ev:+})")
            return

        session.story.append({"role": "user", "content": action_text})
        plot_context = []
        if session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

        cv_prompt = (
            f"Your response MUST be ONLY a single JSON object. A player wants to: '{action_text}'. Analyze this action's potential to fundamentally change the current situation or advance the narrative. Is this a minor, descriptive interaction, or a pivotal, plot-driving moment? A 'trivial' action (CV between -2 and 2) will be narrated as a simple success and will not change the core challenge. A 'critical' action (CV outside -2 and 2) represents an attempt to overcome a real obstacle and MUST change the state of the story. Based on this, respond with a JSON object with one key 'cv' and an integer from -7 (trivial) to +7 (story-altering). Respond ONLY with a JSON object containing a single key 'cv' and an integer from -7 to +7. Do not include any other text."
        )
        cv_payload = plot_context + session.story + [{"role": "user", "content": cv_prompt}]
        cv_json = await get_llm_json_response(client, session, cv_payload)
        cv = cv_json.get("cv", 0) if cv_json else 0
        session.pending_cv = cv

        if -2 <= cv <= 2:
            success_prompt = (
                f"The player's action, '{action_text}', is a simple one that succeeds without needing a roll. "
                "Narrate this successful outcome. It should be a brief, descriptive event that does not significantly alter the plot. "
                "**Your response MUST include fewer than 2,000 words.** "
                "**Your response must NOT offer the player a list of choices or suggested actions.** "
                "Conclude your narrative with only the open-ended question, 'What do you do now?'"
            )
            payload = plot_context + session.story + [{"role": "user", "content": success_prompt}]
            payload = _add_dm_personality_to_payload(session, payload)
            await narrate_rpg_turn(new_msg.channel, session, payload, client, new_msg.reference.resolved)
        else:
            instruction_template = "..." # Omitted for brevity
            
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
            
            stat_payload = plot_context + session.story + [{"role": "system", "content": stat_prompt}]
            response = await client.chat.completions.create(model=model, messages=stat_payload)
            raw_response = response.choices[0].message.content.strip()
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
                logging.info(f"{raw_response}")
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