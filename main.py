# main.py

import asyncio
import json
import logging
import math
import os
import random
import re
import uuid
from contextlib import asynccontextmanager
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from enum import Enum, auto
from typing import Any, Dict, List, Literal, Optional

import httpx
import yaml
from dotenv import find_dotenv, load_dotenv
from fastapi import FastAPI, HTTPException, Request
from fastapi.responses import HTMLResponse, StreamingResponse
from fastapi.staticfiles import StaticFiles
from openai import AsyncOpenAI
from pydantic import BaseModel

# --- Basic Setup ---
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s: %(message)s")
load_dotenv(find_dotenv())

# --- Configuration Loading ---
def get_app_config():
    with open("config.yaml", "r", encoding="utf-8") as f:
        config = yaml.safe_load(f)
    provider_key_map = {p: f"{p.upper().replace('-', '_')}_API_KEY" for p in config.get("providers", {})}
    for provider, env_var in provider_key_map.items():
        if provider in config.get("providers", {}) and os.getenv(env_var):
            config["providers"][provider]["api_key"] = os.getenv(env_var)
    return config

config = get_app_config()
if not config.get("models"):
    raise ValueError("No models are defined in config.yaml.")

curr_model = next(iter(config["models"]))
system_prompt = config["system_prompt"]

active_sessions: Dict[str, 'RPGSession'] = {}
session_last_access: Dict[str, datetime] = {}

# --- RPG State & Data Classes ---
class RPGState(Enum):
    IDLE = auto()
    AWAITING_DESCRIPTION = auto()
    AWAITING_PERSONALITY_CHOICE = auto()
    AWAITING_COMBAT_MODULE_CHOICE = auto()
    AWAITING_GEAR_CHOICE = auto()
    AWAITING_GEAR_DESCRIPTION = auto()
    AWAITING_SPECIAL_MOVE_TARGET = auto()
    AWAITING_GEAR_QUALITY = auto()
    AWAITING_TURN_LIMIT_CHOICE = auto()
    AWAITING_STAT_ACTION_INPUT = auto()
    AWAITING_FV_SPEND = auto()
    GAME_OVER = auto()

STAT_NAMES = ["STR", "DEX", "CON", "INT", "WIS", "CHA"]
COMBAT_STAT_NAMES = ["initiative", "hit_points", "magic_points", "melee_attack", "ranged_attack", "magic_attack", "miracle_attack", "grapple_attack", "physical_defense", "magic_defense"]


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

@dataclass
class CombatStats:
    initiative: int; hit_points: int; magic_points: int; melee_attack: int
    ranged_attack: int; magic_attack: int; miracle_attack: int; grapple_attack: int
    physical_defense: int; magic_defense: int

@dataclass
class GearItem:
    item_type: str; description: str; quality: str; bonus: int
    target_stat: Optional[str] = None; special_effect: Optional[str] = None

@dataclass
class RPGSession:
    session_id: str
    stats: dict[str, int]
    story: list[dict[str, str]]
    state: RPGState = RPGState.IDLE
    combat_stats: Optional[CombatStats] = None
    inventory: List[GearItem] = field(default_factory=list)
    combat_module_enabled: bool = False
    plot_outline: Optional[Dict[str, Any]] = None
    dm_personality: Optional[str] = None
    pending_action_text: Optional[str] = None
    pending_stat_for_action: Optional[str] = None
    pending_dv: Optional[int] = None
    overall_goal: Optional[str] = None
    turn_limit: Optional[int] = None
    current_turn: int = 0
    roll_margins: List[int] = field(default_factory=list)
    high_fv_actions_count: int = 0
    accumulating_value: int = 0
    pending_llm_payload: Optional[list] = None
    pending_roll_summary: Optional[str] = None
    pending_gear_item: Optional[Dict[str, Any]] = None
    gear_iterator: Optional[iter] = None


# --- Helper & Logic Functions ---
def get_openai_client() -> AsyncOpenAI:
    provider, _ = curr_model.split("/", 1)
    api_key = config["providers"][provider].get("api_key")
    base_url = config["providers"][provider].get("base_url")
    return AsyncOpenAI(base_url=base_url, api_key=api_key)

async def _roll_dice(num_dice: int) -> List[int]:
    try:
        async with httpx.AsyncClient() as client:
            url = f"https://www.random.org/integers/?num={num_dice}&min=1&max=6&col=1&base=10&format=plain&rnd=new"
            resp = await client.get(url, timeout=5.0)
            resp.raise_for_status()
            return [int(n) for n in resp.text.splitlines() if n]
    except Exception as e:
        logging.error(f"Could not fetch dice from random.org, using fallback: {e}")
        return [random.randint(1, 6) for _ in range(num_dice)]

async def _roll_erratic_value() -> int:
    dice = await _roll_dice(4)
    return (dice[0] + dice[1]) - (dice[2] + dice[3])

def _calculate_combat_stats(stats: Dict[str, int]) -> CombatStats:
    str_ = stats.get("STR", 0); dex_ = stats.get("DEX", 0); con_ = stats.get("CON", 0)
    int_ = stats.get("INT", 0); wis_ = stats.get("WIS", 0); cha_ = stats.get("CHA", 0)
    initiative = math.floor(dex_ + int_ / 2)
    hp_base = math.floor(str_ + con_ / 2); mp_base = math.floor(wis_ + int_ / 2)
    melee_attack = math.floor(str_ + dex_ / 2); ranged_attack = math.floor(wis_ + dex_ / 2)
    magic_attack = math.floor(int_ + cha_ / 2); miracle_attack = math.floor(wis_ + cha_ / 2)
    grapple_attack = math.floor(str_ + con_ / 2); physical_defense = math.floor(con_ + dex_ / 2)
    magic_defense = math.floor(int_ + wis_ / 2)
    return CombatStats(
        initiative=max(-8, initiative), hit_points=max(-8, hp_base) * 3,
        magic_points=max(-8, mp_base) * 3, melee_attack=max(-8, melee_attack),
        ranged_attack=max(-8, ranged_attack), magic_attack=max(-8, magic_attack),
        miracle_attack=max(-8, miracle_attack), grapple_attack=max(-8, grapple_attack),
        physical_defense=max(-8, physical_defense), magic_defense=max(-8, magic_defense)
    )

def _apply_gear_bonuses(session: RPGSession):
    if not session.combat_stats:
        session.combat_stats = _calculate_combat_stats(session.stats)
    # Reset stats to base before reapplying bonuses
    base_stats = _calculate_combat_stats(session.stats)
    session.combat_stats = base_stats
    for item in session.inventory:
        if item.target_stat and hasattr(session.combat_stats, item.target_stat):
            current_value = getattr(session.combat_stats, item.target_stat)
            setattr(session.combat_stats, item.target_stat, current_value + item.bonus)

def _add_dm_personality_to_payload(session: RPGSession, payload: list, force_vanilla: bool = False) -> list:
    if session.dm_personality and not force_vanilla:
        personality = session.dm_personality.format(date=datetime.now().strftime('%Y-%m-%d'), time=datetime.now().strftime('%H:%M:%S'))
        return [{"role": "system", "content": personality}] + payload
    return payload

async def get_llm_json_response(client: AsyncOpenAI, session: RPGSession, payload: list, retries=3) -> Optional[Dict]:
    _, model = curr_model.split('/', 1)
    for _ in range(retries):
        try:
            response = await client.chat.completions.create(model=model, messages=payload, stream=False, response_format={"type": "json_object"})
            raw_content = response.choices[0].message.content
            try:
                return json.loads(raw_content)
            except json.JSONDecodeError:
                match = re.search(r'```(json)?\s*(\{.*\})\s*```', raw_content, re.DOTALL)
                if match:
                    try: return json.loads(match.group(2))
                    except json.JSONDecodeError: continue
        except Exception as e:
            logging.error(f"Error getting JSON from LLM: {e}. Retrying...")
            await asyncio.sleep(1)
    return None

async def _get_llm_binary_evaluation(client: AsyncOpenAI, action_text: str, eval_type: str) -> bool:
    prompt = f"You are an evaluator of player actions. Determine if the action is '{eval_type}'. 'Creative' means imaginative, clever, or particularly descriptive. Respond with only a single word: YES or NO.\n\nPlayer action: '{action_text}'"
    try:
        _, model = curr_model.split("/", 1)
        response = await client.chat.completions.create(model=model, messages=[{"role": "system", "content": prompt}], stream=False, temperature=0, max_tokens=5)
        return "YES" in response.choices[0].message.content.strip().upper()
    except Exception as e:
        logging.error(f"Error during LLM binary evaluation for {eval_type}: {e}")
        return False

# --- Streaming & Session Management ---

@asynccontextmanager
async def lifespan(app: FastAPI):
    asyncio.create_task(cleanup_inactive_sessions())
    yield

async def cleanup_inactive_sessions():
    while True:
        await asyncio.sleep(600)
        now = datetime.now(timezone.utc)
        inactive_ids = [sid for sid, t in session_last_access.items() if (now - t).total_seconds() > 3600]
        for sid in inactive_ids:
            if sid in active_sessions: del active_sessions[sid]
            if sid in session_last_access: del session_last_access[sid]
            logging.info(f"Cleaned up inactive session: {sid}")

async def stream_llm_response_sse(session: RPGSession, llm_payload: list):
    full_response_content = ""
    client = get_openai_client()
    try:
        _, model = curr_model.split("/", 1)
        params = config["models"].get(curr_model, {})
        final_payload = _add_dm_personality_to_payload(session, llm_payload)
        stream = await client.chat.completions.create(model=model, messages=final_payload, stream=True, **params)
        async for chunk in stream:
            delta = chunk.choices[0].delta.content or ""
            if delta:
                full_response_content += delta
                yield f"data: {json.dumps({'type': 'chunk', 'content': delta})}\n\n"
        session.story.append({"role": "assistant", "content": full_response_content})
    except Exception as e:
        logging.exception("Error streaming LLM response")
        yield f"data: {json.dumps({'type': 'error', 'content': f'An error occurred: {e}'})}\n\n"
    finally:
        yield f"data: {json.dumps({'type': 'end', 'content': full_response_content})}\n\n"

app = FastAPI(lifespan=lifespan)
app.mount("/static", StaticFiles(directory="static"), name="static")

# --- Pydantic Models ---
class StartGameRequest(BaseModel):
    consent_given: bool; stats: Dict[str, int]

class ActionRequest(BaseModel):
    session_id: str; action_type: Literal["text", "button"]; value: str

# --- API Endpoints ---
@app.get("/", response_class=HTMLResponse)
async def read_root():
    with open("index.html", "r", encoding="utf-8") as f:
        return HTMLResponse(content=f.read())

@app.post("/api/start_game")
async def start_game(req: StartGameRequest):
    if not req.consent_given: raise HTTPException(403, "Consent not given.")
    session_id = str(uuid.uuid4())
    session = RPGSession(
        session_id=session_id, stats=req.stats,
        story=[
            {"role": "system", "content": "You are a Dungeon Master for a one-shot RPG adventure."},
            {"role": "system", "content": f"The player's character stats are: { ' | '.join(f'{s}: {v:+}' for s, v in req.stats.items()) }"}
        ],
        state=RPGState.AWAITING_DESCRIPTION
    )
    active_sessions[session_id] = session
    session_last_access[session_id] = datetime.now(timezone.utc)
    return {
        "session_id": session_id,
        "message": "Character created! Please reply with a brief description of your character (name, appearance, backstory), or type 'skip'.",
        "state": session.state.name
    }

@app.get("/api/stream/{session_id}")
async def stream_events(session_id: str):
    if session_id not in active_sessions: raise HTTPException(404, "Session not found.")
    session = active_sessions[session_id]
    session_last_access[session_id] = datetime.now(timezone.utc)
    if not session.pending_llm_payload:
        async def empty_stream(): yield f"data: {json.dumps({'type': 'error', 'content': 'No pending action.'})}\n\n"
        return StreamingResponse(empty_stream(), media_type="text/event-stream")
    llm_payload = session.pending_llm_payload
    session.pending_llm_payload = None
    return StreamingResponse(stream_llm_response_sse(session, llm_payload), media_type="text/event-stream")

async def finalize_setup_and_start_game(session: RPGSession, client: AsyncOpenAI):
    session.story.append({"role": "system", "content": f"The adventure will have a turn limit of {session.turn_limit}."})
    if session.combat_module_enabled:
        _apply_gear_bonuses(session)
        session.story.append({"role": "system", "content": "Combat module is ON."})
        inventory_str = json.dumps([asdict(item) for item in session.inventory])
        session.story.append({"role": "system", "content": f"Player inventory: {inventory_str}"})
    else:
        session.story.append({"role": "system", "content": "Combat module is OFF."})
    plot_prompt = ("Create a JSON object for a one-shot RPG adventure. The player is the protagonist. "
                   "Provide a 'title', a 'goal' for the player, a one-sentence 'inciting_incident', "
                   "and an 'antagonist' object with a 'name' and 'description'.\n"
                   f"Base the theme on the player's description and stats: {session.stats}")
    plot_json = await get_llm_json_response(client, session, session.story + [{"role": "system", "content": plot_prompt}])
    session.plot_outline = plot_json if plot_json else {"title": "A Simple Quest", "goal": "Find the missing artifact.", "inciting_incident": "You are hired to find a missing artifact.", "antagonist": {"name": "A mysterious thief", "description": "A shadowy figure."}}
    session.overall_goal = session.plot_outline.get("goal")
    session.story.append({"role": "system", "content": f"SECRET PLOT INFO (for DM only): {json.dumps(session.plot_outline)}"})
    intro_prompt = (f"Begin the adventure. The title is '{session.plot_outline.get('title', 'A Simple Quest')}'. "
                    f"Narrate the inciting incident: '{session.plot_outline.get('inciting_incident', '')}'. "
                    "Describe the scene and the immediate situation. Conclude with 'What do you do?'")
    session.pending_llm_payload = session.story + [{"role": "system", "content": intro_prompt}]
    session.state = RPGState.IDLE
    return {"action": "listen_for_stream", "message": "Let the adventure begin..."}

def get_session_ui_data(session: RPGSession) -> Dict[str, Any]:
    """Helper to assemble all UI-relevant data."""
    data = {
        "state": session.state.name,
        "turn": session.current_turn,
        "turn_limit": session.turn_limit,
        "fate_pool": session.accumulating_value,
        "stats": session.stats,
    }
    if session.combat_module_enabled and session.combat_stats:
        data["combat_stats"] = asdict(session.combat_stats)
    return data

@app.post("/api/game_action")
async def game_action(req: ActionRequest):
    if req.session_id not in active_sessions: raise HTTPException(404, "Session not found.")
    session = active_sessions[req.session_id]
    session_last_access[req.session_id] = datetime.now(timezone.utc)
    client = get_openai_client()
    response = {}

    # --- SETUP STATES ---
    if session.state == RPGState.AWAITING_DESCRIPTION:
        if req.value.strip().lower() not in ['no', 'n', 'skip']:
            session.story.append({"role": "system", "content": f"Player description: \"{req.value}\""})
        session.state = RPGState.AWAITING_PERSONALITY_CHOICE
        response = {"message": "The default Dungeon Master has a specific personality. Would you like to use this custom personality for your adventure?", "buttons": [{"text": "Yes, please", "id": "p_yes"}, {"text": "No, thanks (vanilla)", "id": "p_no"}]}
    elif session.state == RPGState.AWAITING_PERSONALITY_CHOICE:
        if req.value == 'p_yes': session.dm_personality = system_prompt
        session.state = RPGState.AWAITING_COMBAT_MODULE_CHOICE
        response = {"message": "Do you want to **activate the combat module?**\n\nIf **Yes**, actions will be evaluated for combat and you can select gear.\nIf **No**, all situations will be narrative and you forgo equipment.", "buttons": [{"text": "Yes, Activate", "id": "cm_yes"}, {"text": "No, Keep it Narrative", "id": "cm_no"}]}
    elif session.state == RPGState.AWAITING_COMBAT_MODULE_CHOICE:
        session.combat_module_enabled = (req.value == 'cm_yes')
        if session.combat_module_enabled:
            session.combat_stats = _calculate_combat_stats(session.stats)
            session.gear_iterator = iter(GEAR_CATALOG.items())
            session.state = RPGState.AWAITING_GEAR_CHOICE
            return await game_action(ActionRequest(session_id=req.session_id, action_type='button', value='continue'))
        else:
            session.state = RPGState.AWAITING_TURN_LIMIT_CHOICE
            return await game_action(ActionRequest(session_id=req.session_id, action_type='button', value='continue'))
    elif session.state == RPGState.AWAITING_GEAR_CHOICE:
        try:
            item_type, item_data = next(session.gear_iterator)
            session.pending_gear_item = {"item_type": item_type, "target_stat": item_data.get("target")}
            session.state = RPGState.AWAITING_GEAR_DESCRIPTION
            response = {"message": f"**Select your {item_type}:**\n_{item_data['desc']}_\n\nPlease describe it briefly (e.g., 'a rusty iron longsword', 'a pair of sleek, silent boots'). Or type `skip`."}
        except StopIteration:
            session.state = RPGState.AWAITING_TURN_LIMIT_CHOICE
            return await game_action(ActionRequest(session_id=req.session_id, action_type='button', value='continue'))
    elif session.state == RPGState.AWAITING_GEAR_DESCRIPTION:
        if req.value.strip().lower() == 'skip':
            session.state = RPGState.AWAITING_GEAR_CHOICE
            return await game_action(ActionRequest(session_id=req.session_id, action_type='button', value='continue'))
        session.pending_gear_item['description'] = req.value
        if session.pending_gear_item['item_type'] == "Special Move":
            session.state = RPGState.AWAITING_SPECIAL_MOVE_TARGET
            buttons = [{"text": f"{name} ({val:+})", "id": f"stat_{name}"} for name, val in session.stats.items()]
            response = {"message": "Which base stat does your Special Move draw upon for its bonus?", "buttons": buttons}
        else:
            session.state = RPGState.AWAITING_GEAR_QUALITY
            buttons = [{"text": "Standard (+1)", "id": "q_1"}, {"text": "Quality (+2)", "id": "q_2"}, {"text": "Masterwork (+3)", "id": "q_3"}]
            response = {"message": "What is the quality of this item?", "buttons": buttons}
    elif session.state == RPGState.AWAITING_SPECIAL_MOVE_TARGET:
        stat_name = req.value.split('_')[1]
        target_map = {"STR": "melee_attack", "DEX": "ranged_attack", "INT": "magic_attack", "WIS": "miracle_attack", "CON": "physical_defense", "CHA": "magic_defense"}
        session.pending_gear_item['target_stat'] = target_map.get(stat_name, "melee_attack")
        session.state = RPGState.AWAITING_GEAR_QUALITY
        buttons = [{"text": "Standard (+1)", "id": "q_1"}, {"text": "Quality (+2)", "id": "q_2"}, {"text": "Masterwork (+3)", "id": "q_3"}]
        response = {"message": "What is the quality of your Special Move?", "buttons": buttons}
    elif session.state == RPGState.AWAITING_GEAR_QUALITY:
        quality_map = {"q_1": ("Standard", 1), "q_2": ("Quality", 2), "q_3": ("Masterwork", 3)}
        quality, bonus = quality_map.get(req.value, ("Standard", 1))
        session.pending_gear_item['quality'] = quality
        session.pending_gear_item['bonus'] = bonus
        item = GearItem(**session.pending_gear_item)
        session.inventory.append(item)
        _apply_gear_bonuses(session)
        session.pending_gear_item = None
        response = {"message": f"Added **{item.quality} {item.item_type}** (+{item.bonus} to {item.target_stat.replace('_', ' ').title()}) to your inventory."}
        session.state = RPGState.AWAITING_GEAR_CHOICE
        # This feels clunky, but it's to force the next step in the gear selection loop async
        asyncio.create_task(httpx.post(str(req.url_for('game_action')), json={"session_id": req.session_id, "action_type": "button", "value": "continue"}))
    elif session.state == RPGState.AWAITING_TURN_LIMIT_CHOICE:
        if req.value.startswith('t_'):
            session.turn_limit = int(req.value.split('_')[1])
            response = await finalize_setup_and_start_game(session, client)
        else:
            response = {"message": "Finally, how long should our adventure be? A shorter game is more focused, a longer one more exploratory.", "buttons": [{"text": "Short (~15 turns)", "id": "t_15"}, {"text": "Medium (~25 turns)", "id": "t_25"}, {"text": "Long (~40 turns)", "id": "t_40"}]}

    # --- MAIN GAME LOOP STATES ---
    elif session.state == RPGState.IDLE:
        # Player chose a stat to act with
        stat = req.value.upper()
        if stat in STAT_NAMES:
            session.pending_stat_for_action = stat
            session.state = RPGState.AWAITING_STAT_ACTION_INPUT
            response = {"message": f"What do you do using **{stat}**?"}
        elif stat == 'USE_FATE':
            session.state = RPGState.AWAITING_FV_SPEND
            response = {"message": f"You have **{session.accumulating_value}** in your Fate Pool. How much do you want to spend to influence the outcome of your next action? (Enter a number)"}

    elif session.state == RPGState.AWAITING_FV_SPEND:
        try:
            spend = int(req.value)
            if 0 < spend <= session.accumulating_value:
                session.accumulating_value -= spend
                # This is a placeholder; the value will be used in the next roll
                # For now, just return to idle to let the user choose an action.
                # A more robust system might store this pending spend value.
                session.state = RPGState.IDLE
                response = {"message": f"You've committed **{spend}** from your Fate Pool. Now, choose your action."}
            else:
                response = {"message": f"Invalid amount. Please enter a number between 1 and {session.accumulating_value}."}
        except ValueError:
            response = {"message": "Please enter a valid number."}


    elif session.state == RPGState.AWAITING_STAT_ACTION_INPUT:
        action_text = req.value
        session.story.append({"role": "user", "content": action_text})
        session.current_turn += 1
        stat = session.pending_stat_for_action
        
        # Determine DV with LLM
        dv_prompt = f"A player performs an action using their {stat} stat: '{action_text}'. Determine a Difficulty Value (DV) from -7 (trivial) to +7 (impossible) for a normal human. Respond ONLY with a single number. Example: '3' or '-2'"
        _, model = curr_model.split('/', 1)
        dv_response_raw = await client.chat.completions.create(model=model, messages=[{"role":"system", "content":dv_prompt}], stream=False, temperature=0, max_tokens=5)
        raw_response = dv_response_raw.choices[0].message.content.strip()
        try:
            dv = int(re.search(r'(-?\d+)', raw_response).group(1))
        except (ValueError, AttributeError):
            dv = 0 # Default DV if LLM fails

        # Perform Rolls
        stat_bonus = session.stats.get(stat, 0)
        d1, d2 = await _roll_dice(2)
        roll_result = d1 - d2
        margin = (stat_bonus + roll_result) - dv
        fv = await _roll_erratic_value()

        # Evaluate Creativity and Update Fate Pool
        is_creative = await _get_llm_binary_evaluation(client, action_text, "Creative")
        fv_message = f"Fate Value (FV) roll: `{fv}`."
        if is_creative:
            session.accumulating_value += fv
            fv_message += f"\n**Creative action!** FV added to your Fate Pool. Pool is now: `{session.accumulating_value}`."
        if abs(fv) >= 7:
            session.high_fv_actions_count += 1

        # Determine Outcome
        outcome_level = "Failure"
        if margin >= 5: outcome_level = "Critical Success"
        elif margin >= 0: outcome_level = "Success"
        
        session.roll_margins.append(margin)

        summary = (f"**Turn {session.current_turn}/{session.turn_limit} | Action: {stat}**\n"
                   f"**Player Action:** *{action_text}*\n"
                   f"**Roll:** `{stat}` ({stat_bonus:+}) + `d6-d6` ({d1}-{d2} = {roll_result:+}) vs `DV` ({dv})\n"
                   f"**Result:** {stat_bonus + roll_result} vs {dv} -> **{outcome_level}** (Margin: {margin})\n---\n{fv_message}")

        outcome_prompt = f"The player's action, '{action_text}', was resolved with a roll. The outcome was a '{outcome_level}' with a success/failure margin of {margin}. The Fate Value for this turn was {fv}. Narrate the result of this action based on these factors. Be descriptive. Conclude with 'What do you do now?'"
        
        session.pending_llm_payload = session.story + [{"role": "system", "content": outcome_prompt}]
        session.state = RPGState.IDLE
        response = {"action": "listen_for_stream", "roll_summary": summary}
        
    if not response:
        response = {"error": f"Unhandled game state: {session.state.name}"}

    # Attach UI data to every response
    response.update(get_session_ui_data(session))
    return response