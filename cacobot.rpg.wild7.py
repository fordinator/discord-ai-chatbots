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
import chess
import urllib.parse

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

def is_in_allowed_channel():
    async def predicate(interaction: discord.Interaction) -> bool:
        allowed_channel_ids = config.get("permissions", {}).get("channels", {}).get("allowed_ids", {})
        if not allowed_channel_ids:
            return True
        return interaction.channel_id in allowed_channel_ids
    return app_commands.check(predicate)

@discord_bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.CheckFailure):
        await interaction.response.send_message("⚠️ You can only use this command in the designated channel.", ephemeral=True)
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
    state: RPGState = RPGState.IDLE
    pending_action_text: Optional[str] = None
    pending_stat_for_action: Optional[str] = None
    pending_cv: Optional[int] = None
    pending_dv: Optional[int] = None

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
        
        self.session.story.append({"role": "user", "content": f"I will {button_label}"})
        outcome_prompt = f"The player chose the stock action: '{button_label}'\nAs the Dungeon Master, describe this outcome in a narrative and engaging way. No significant events take place, the result succeeds but is only descriptive. No significant change occurs in the plot, nor does the player really advance or impede any of their goals. Do not mention dice, stats, or numbers. Conclude by asking the player what they do next."
        provider, model = curr_model.split("/", 1)
        openai_client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

        # ADDED: Include plot outline in payload
        plot_context = []
        if self.session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(self.session.plot_outline)}"})

        llm_payload = plot_context + self.session.story + [{"role": "system", "content": outcome_prompt}]
        await narrate_rpg_turn(interaction.channel, self.session, llm_payload, openai_client, interaction.message)

async def get_llm_json_response(client: AsyncOpenAI, payload: list, retries=3) -> Any:
    for _ in range(retries):
        try:
            response = await client.chat.completions.create(model=curr_model.split('/', 1)[1], messages=payload, stream=False, response_format={"type": "json_object"})
            return json.loads(response.choices[0].message.content)
        except Exception as e:
            logging.error(f"Error getting JSON from LLM: {e}. Retrying...")
            await asyncio.sleep(1)
    return None

# MODIFIED: Added event_notification parameter
async def narrate_rpg_turn(channel: discord.TextChannel, session: RPGSession, llm_payload: list, client: AsyncOpenAI, message_to_reply: discord.Message, roll_details_text: str = "", event_notification: Optional[str] = None):
    try:
        embed = discord.Embed(description=STREAMING_INDICATOR, color=EMBED_COLOR_INCOMPLETE)
        response_msg = await message_to_reply.reply(embed=embed, silent=True)
        narrative = await stream_llm_response(channel, response_msg, llm_payload, client)
        session.story.append({"role": "assistant", "content": narrative})
        
        trivial_actions_prompt = "Based on the last scene description, suggest three distinct, simple, one-sentence actions a player could take. These actions should be trivial and not require a skill check. Respond *only* with a valid JSON object containing a single key 'actions' with a list of 1-3 strings. Example: {\"actions\": [\"Look under the bed.\", \"Open the window.\", \"Listen at the door.\"]}"
        
        # ADDED: Include plot outline for trivial action generation
        plot_context = []
        if session.plot_outline:
            plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})
        
        actions_payload = plot_context + session.story + [{"role": "system", "content": trivial_actions_prompt}]
        actions_json = await get_llm_json_response(client, actions_payload)
        trivial_actions = actions_json.get("actions", []) if isinstance(actions_json, dict) else []
        
        # MODIFIED: Handle the event_notification
        narrative_with_event = narrative
        if event_notification:
            narrative_with_event = f"{narrative}\n\n**{event_notification}**"

        final_description = f"{narrative_with_event}\n\n{roll_details_text}" if roll_details_text else narrative_with_event

        final_embed = discord.Embed(description=final_description, color=EMBED_COLOR_RPG)
        
        await response_msg.edit(embed=final_embed, view=RPGActionView(session, trivial_actions))
        session.state = RPGState.IDLE
        session.pending_action_text = session.pending_stat_for_action = session.pending_cv = session.pending_dv = None
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

# ADDED: Function to roll for Erratic Value, adapted from rpg.wild
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
        self._update_dice_buttons()
        await interaction.response.edit_message(view=self)

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
                customize_view = CustomizeStatView(self.original_interaction, stat_name, initial_signed_dice, self)
                await inner_interaction.response.edit_message(content=f"Customizing **{stat_name}**. Click buttons to flip signs.", view=customize_view)

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

@rpg_group.command(name="rollchar", description="Create a character with randomly generated stats.")
@is_in_allowed_channel()
async def rpg_rollchar(interaction: discord.Interaction):
    if interaction.channel_id in rpg_sessions:
        await interaction.response.send_message("⚠️ An RPG session is already active in this channel.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    view = StatGenerationView(original_interaction=interaction)
    await view.start()
    await view.wait()

    if view.final_stats:
        stats, user = view.final_stats, interaction.user
        session = RPGSession(user_id=user.id, user_mention=user.mention, stats=stats, story=[
            {"role": "system", "content": "You are a Dungeon Master for a one-shot RPG adventure."},
            {"role": "system", "content": f"The player's character stats are: { ' | '.join(f'{s}: {v:+}' for s, v in stats.items()) }"}
        ])
        rpg_sessions[interaction.channel_id] = session
        session.state = RPGState.AWAITING_DESCRIPTION
        prompt_message = (f"**Your character is ready, {user.mention}!**\n\n"
                        "Before we begin, would you like to provide a brief description of your character? "
                        "This could be their name, appearance, or a bit of their backstory.\n\n"
                        "**Please reply to this message with your description.** (Or reply with `skip` if you'd rather not.)")
        await interaction.channel.send(prompt_message)

@rpg_group.command(name="roll", description="Roll the dice to perform an action.")
@is_in_allowed_channel()
async def rpg_roll(interaction: discord.Interaction):
    session = rpg_sessions.get(interaction.channel_id)
    if not session:
        await interaction.response.send_message("⚠️ There is no active RPG session in this channel.", ephemeral=True)
        return
    if interaction.user.id != session.user_id:
        await interaction.response.send_message("⚠️ It's not your turn to roll.", ephemeral=True)
        return
    if session.state != RPGState.AWAITING_ROLL:
        await interaction.response.send_message("⚠️ There is no action pending a roll.", ephemeral=True)
        return
    await interaction.response.defer()
    dice_rolls = await _roll_dice(8)
    if not dice_rolls or len(dice_rolls) < 8:
        await interaction.followup.send("❌ Error rolling dice. Please try again.", ephemeral=True)
        return
    
    pos, neg = sum(dice_rolls[:4]), sum(dice_rolls[4:])
    stat_bonus = session.stats[session.pending_stat_for_action]
    final_result = (pos - neg) + stat_bonus
    dv, cv = session.pending_dv, session.pending_cv
    margin = final_result - dv
    
    outcomes = {7: "Amazing success", 5: "Great success", 3: "OK success", 1: "Near success", 
                -1: "Near failure", -3: "Kinda bad failure", -5: "Bad failure", -999: "Terrible failure"}
    outcome_desc = next(v for k, v in sorted(outcomes.items(), reverse=True) if margin >= k)

    summary_msg = await interaction.followup.send(content="*Dice hit the table...*", wait=True)
    # Updated code for the rpg_roll function

    roll_summary = (f"**Action:** *{session.pending_action_text}*\n"
                    f"**Check:** {session.pending_stat_for_action} `({stat_bonus:+})` vs **DV** `{dv}` (CV: {cv:+})\n"
                     f"**Roll:** `[{pos} - {neg}] + {stat_bonus} =` **{final_result}** | **Margin:** {margin:+} | **Outcome:** {outcome_desc}")

    outcome_prompt = (f"The player attempted: '{session.pending_action_text}'. This required a {session.pending_stat_for_action} check. "
                      f"The result was: '{outcome_desc}'. As the DM, describe this outcome narratively. Do not mention dice, stats, or numbers. "
                      f"Conclude by asking what they do next.")
    
    provider, model = curr_model.split("/", 1)
    client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))
    session.story.append({"role": "user", "content": session.pending_action_text})

    # ADDED: Include plot outline in payload
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

    llm_payload = plot_context + session.story + [{"role": "system", "content": outcome_prompt}]
    
    await narrate_rpg_turn(interaction.channel, session, llm_payload, client, summary_msg, roll_details_text=roll_summary)
    await summary_msg.edit(content=f"Roll processed for action: *{session.pending_action_text}*")

@rpg_group.command(name="conclude", description="Ends the current RPG session.")
@is_in_allowed_channel()
async def rpg_conclude(interaction: discord.Interaction):
    session = rpg_sessions.get(interaction.channel_id)
    if not session or interaction.user.id != session.user_id:
        await interaction.response.send_message("⚠️ No active session for you to conclude here.", ephemeral=True)
        return
    await interaction.response.defer()
    conclusion_prompt = "The player has ended the session. Based on the story, provide a concluding narrative, wrapping up the current scene with a brief but satisfying end."
    provider, model = curr_model.split("/", 1)
    client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))
    
    # ADDED: Include plot outline in payload
    plot_context = []
    if session.plot_outline:
        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

    llm_payload = plot_context + session.story + [{"role": "system", "content": conclusion_prompt}]
    reply_target = await interaction.channel.send("Concluding the adventure...")
    try:
        await stream_llm_response(interaction.channel, reply_target, llm_payload, client)
    except Exception as e:
        logging.error(f"Error during RPG conclusion: {e}")
    finally:
        if interaction.channel_id in rpg_sessions:
            del rpg_sessions[interaction.channel_id]
        await interaction.followup.send("✅ **The RPG session has now concluded.**", ephemeral=True)
        
discord_bot.tree.add_command(rpg_group)

@discord_bot.event
async def on_message(new_msg: discord.Message):
    if new_msg.author.bot: return
    
    if session := rpg_sessions.get(new_msg.channel.id):
        is_player = new_msg.author.id == session.user_id
        is_reply_to_bot = new_msg.reference and new_msg.reference.resolved and new_msg.reference.resolved.author == discord_bot.user
        
        if is_player and is_reply_to_bot:
            # --- MODIFIED: AWAITING_DESCRIPTION block with Plot Generation ---
            if session.state == RPGState.AWAITING_DESCRIPTION:
                await new_msg.reference.resolved.delete()
                
                description_text = ""
                description_provided = False
                if new_msg.content.strip().lower() not in ['no', 'n', 'skip']:
                    description_text = new_msg.content
                    session.story.append({"role": "system", "content": f"Player description: \"{description_text}\""})
                    description_provided = True

                await new_msg.delete()
                await new_msg.channel.send(content="*The threads of fate are weaving a secret destiny for you...*", silent=True)

                provider, model = curr_model.split("/", 1)
                client = AsyncOpenAI(base_url=config["providers"][provider]["base_url"], api_key=config["providers"][provider].get("api_key", "sk-no-key-required"))

                character_context = f"The player's character is described as follows: '{description_text}'" if description_provided else "The player has not provided a character description."
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
                plot_json = await get_llm_json_response(client, plot_payload)

                if plot_json:
                    session.plot_outline = plot_json
                    logging.info(f"Generated plot outline for session in channel {new_msg.channel.id}")
                else:
                    logging.error(f"Failed to generate plot outline for session in channel {new_msg.channel.id}")
                    await new_msg.channel.send("⚠️ Failed to generate the story's fate. The adventure will be purely improvised.")

                ack_msg = "Your character description has been recorded and your destiny set." if description_provided else "No description provided. A mysterious destiny has been set."
                initial_story_message = await new_msg.channel.send(f"{ack_msg}\nThe adventure is about to begin...")
                
                dungeon_master_prompt = "You are a Dungeon Master. Describe an immersive opening scene for the player. Introduce the environment and any NPCs. Conclude by asking the player what they would like to do. Do not ask for a roll or determine any outcomes yet."
                
                plot_context = []
                if session.plot_outline:
                    plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

                llm_payload = plot_context + session.story + [{"role": "system", "content": dungeon_master_prompt}]
                await narrate_rpg_turn(new_msg.channel, session, llm_payload, client, initial_story_message)
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

                # --- ADDED: ERRATIC VALUE (EV) CHECK ---
                ev = await _roll_erratic_value()
                if ev < -6 or ev > 6:
                    session.story.append({"role": "user", "content": action_text}) # Add action to story for context
                    plot_context = []
                    if session.plot_outline:
                        plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})
                    
                    erratic_event_prompt = (
                        f"An 'ERRATIC EVENT' has been triggered (EV: {ev})! The player just tried to: '{action_text}'. You MUST now narrate a COMPLETELY UNEXPECTED and wild turn of events. This event should be related to the player's action and the overall story, but it must throw the narrative off balance. It can be good, bad, or bizarre, but it must be a major narrative twist. Describe this shocking development, and then ask the player what they do in response to this chaos.\n"
                    )
                    payload = plot_context + session.story + [{"role": "system", "content": erratic_event_prompt}]
                    # Call narrate_rpg_turn with the new event notification
                    await narrate_rpg_turn(new_msg.channel, session, payload, client, new_msg.reference.resolved, event_notification=f"ERRATIC EVENT!! (EV: {ev:+})")
                    return # End processing for this message

                # --- REGULAR ACTION FLOW CONTINUES ---
                session.story.append({"role": "user", "content": action_text})

                plot_context = []
                if session.plot_outline:
                    plot_context.append({"role": "system", "content": f"SECRET DM PLOT OUTLINE: {json.dumps(session.plot_outline)}"})

                cv_prompt = f"Player action: '{action_text}'. How critical is this to the story? Respond with a JSON object with one key 'cv' and an integer from -7 (trivial) to +7 (story-altering). Example: {{\"cv\": 3}}"
                cv_payload = plot_context + [{"role": "system", "content": cv_prompt}]
                cv_json = await get_llm_json_response(client, cv_payload)
                cv = cv_json.get("cv", 0) if cv_json else 0
                session.pending_cv = cv

                if -2 <= cv <= 2:
                    success_prompt = f"The player's trivial action, '{action_text}', succeeds. Describe the simple, positive outcome. Ask what they do next."
                    payload = plot_context + session.story + [{"role": "system", "content": success_prompt}]
                    await narrate_rpg_turn(new_msg.channel, session, payload, client, new_msg.reference.resolved)
                else:
                    if session.state == RPGState.AWAITING_STAT_ACTION_INPUT:
                        stat_to_use = session.pending_stat_for_action
                        stat_prompt = f"Player action: '{action_text}' using {stat_to_use}. Determine a base Difficulty (DV) from -7 to +7. Respond ONLY with '{stat_to_use},DV'. Example: '{stat_to_use},3'"
                    else:
                        stat_prompt = f"Player action: '{action_text}'. Which stat is most relevant (STR, DEX, CON, INT, WIS, CHA)? Determine a base Difficulty (DV) from -7 to +7. Respond ONLY with 'STAT,DV'. Example: 'DEX,3'"
                    
                    stat_payload = plot_context + session.story + [{"role": "system", "content": stat_prompt}]
                    response = await client.chat.completions.create(model=model, messages=stat_payload)
                    raw_response = response.choices[0].message.content.strip()
                    match = re.search(r'([A-Z]{3}),\s*(-?\d+)', raw_response)

                    if match:
                        stat, dv_str = match.groups()
                        final_dv = int(dv_str) + (cv // 2 if abs(cv) >= 5 else 0)
                        session.pending_stat_for_action, session.pending_dv, session.state = stat.upper(), final_dv, RPGState.AWAITING_ROLL
                        criticality_text = "**CRITICAL ACTION**" if abs(cv) >= 5 else "Action"
                        await new_msg.channel.send(f"{session.user_mention}, {criticality_text} requires a **{stat.upper()}** check vs **DV {final_dv}** (CV: {cv:+}).\n> *{action_text}*\nUse `/rpg roll`.")
                    else:
                        await new_msg.channel.send(f"I couldn't determine the check for your action (got: `{raw_response}`). Please rephrase and reply to my last message.")
                        session.story.pop()
                        session.state = RPGState.IDLE
                return

# The rest of the file is unchanged from cacobot.rpg.only6.py
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
    
@discord_bot.tree.command(name="reset", description="Reset the system prompt")
async def reset(interaction: discord.Interaction):
    global system_prompt
    system_prompt = config["system_prompt"]
    await interaction.response.send_message("**System prompt reset.**", ephemeral=True)

@discord_bot.tree.command(name="system", description="Change the system prompt")
async def system(interaction: discord.Interaction, prompt: str):
    global system_prompt
    system_prompt = prompt
    await interaction.response.send_message(f"**System prompt updated.**", ephemeral=True)

@discord_bot.tree.command(name="model", description="View or switch the current model")
async def model_command(interaction: discord.Interaction, model: Optional[str] = None):
    global curr_model
    if model is None:
        await interaction.response.send_message(f"Current model is `{curr_model}`.", ephemeral=True)
        return
    user_is_admin = interaction.user.id in config.get("permissions", {}).get("users", {}).get("admin_ids", [])
    if user_is_admin:
        if model in config.get("models", {}):
            curr_model = model
            await interaction.response.send_message(f"Model switched to: `{model}`", ephemeral=True)
        else:
            await interaction.response.send_message("⚠️ That model is not available.", ephemeral=True)
    else:
        await interaction.response.send_message("🚫 You don't have permission to change the model.", ephemeral=True)

@model_command.autocomplete("model")
async def model_autocomplete(interaction: discord.Interaction, current: str) -> list[Choice[str]]:
    all_models = config.get("models", {})
    choices = [Choice(name=m, value=m) for m in all_models if current.lower() in m.lower()]
    if curr_model not in [c.value for c in choices]:
        choices.insert(0, Choice(name=f"◉ {curr_model} (current)", value=curr_model))
    return choices[:25]

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