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
# MODIFIED: Use find_dotenv() for robust path discovery
load_dotenv(find_dotenv())

# --- Configuration Loading ---
def get_app_config():
    with open("config.yaml", "r", encoding="utf-8") as f:
        config = yaml.safe_load(f)

    provider_key_map = {
        "openai": "OPENAI_API_KEY", "x-ai": "X_AI_API_KEY", "mistral": "MISTRAL_API_KEY",
        "groq": "GROQ_API_KEY", "openrouter": "OPENROUTER_API_KEY",
    }
    for provider, env_var in provider_key_map.items():
        if provider in config.get("providers", {}) and os.getenv(env_var):
            config["providers"][provider]["api_key"] = os.getenv(env_var)
    return config

config = get_app_config()

# MODIFIED: Add validation check for models in config
if not config.get("models"):
    logging.critical("Configuration Error: No models are defined in config.yaml.")
    raise ValueError("No models are defined in config.yaml. Please add at least one model.")

curr_model = next(iter(config["models"]))
system_prompt = config["system_prompt"]

active_sessions: Dict[str, 'RPGSession'] = {}
session_last_access: Dict[str, datetime] = {}

# --- Core RPG Classes (from dm.bot.score5.py, unchanged) ---
class RPGState(Enum):
    IDLE = auto()
    AWAITING_ROLL = auto()
    AWAITING_STAT_ACTION_INPUT = auto()
    AWAITING_DESCRIPTION = auto()

STAT_NAMES = ["STR", "DEX", "CON", "INT", "WIS", "CHA"]

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
    user_id: str
    stats: dict[str, int]
    story: list[dict[str, str]]
    session_id: str
    # --- NEW FIELD TO HOLD PENDING PAYLOAD ---
    pending_llm_payload: Optional[list] = None 
    combat_stats: Optional[CombatStats] = None
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
    accumulating_value: int = 0


# --- Helper Functions (No changes needed here) ---
async def _roll_dice(num_dice: int) -> Optional[List[int]]:
    try:
        async with httpx.AsyncClient() as client:
            url = f"https://www.random.org/integers/?num={num_dice}&min=1&max=6&col=1&base=10&format=plain&rnd=new"
            resp = await client.get(url, timeout=5.0)
            resp.raise_for_status()
            return [int(n) for n in resp.text.splitlines() if n]
    except Exception as e:
        logging.error(f"Could not fetch dice rolls from random.org, using fallback: {e}")
        return [random.randint(1, 6) for _ in range(num_dice)]

def _calculate_combat_stats(stats: Dict[str, int]) -> 'CombatStats':
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

def _add_dm_personality_to_payload(session: 'RPGSession', payload: list[dict[str, Any]], force_vanilla: bool = False) -> list[dict[str, Any]]:
    if session.dm_personality and not force_vanilla:
        personality = session.dm_personality.format(date=datetime.now().strftime('%Y-%m-%d'), time=datetime.now().strftime('%H:%M:%S'))
        personality_prompt = {"role": "system", "content": personality}
        return [personality_prompt] + payload
    return payload

async def stream_llm_response_sse(session: RPGSession, llm_payload: list[dict[str, Any]]):
    full_response_content = ""
    try:
        provider, model = curr_model.split("/", 1)
        api_key = config["providers"][provider].get("api_key")
        base_url = config["providers"][provider].get("base_url")
        client = AsyncOpenAI(base_url=base_url, api_key=api_key)
        
        params = config["models"].get(curr_model, {})
        stream = await client.chat.completions.create(model=model, messages=llm_payload, stream=True, **params)
        
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
        session.state = RPGState.IDLE
        yield f"data: {json.dumps({'type': 'end', 'content': full_response_content})}\n\n"

# --- Session Cleanup ---
async def cleanup_inactive_sessions():
    while True:
        await asyncio.sleep(60 * 10) 
        now = datetime.now(timezone.utc)
        inactive_session_ids = [
            sid for sid, last_time in session_last_access.items()
            if (now - last_time).total_seconds() > 3600
        ]
        for sid in inactive_session_ids:
            if sid in active_sessions: del active_sessions[sid]
            if sid in session_last_access: del session_last_access[sid]
            logging.info(f"Cleaned up inactive session: {sid}")

@asynccontextmanager
async def lifespan(app: FastAPI):
    asyncio.create_task(cleanup_inactive_sessions())
    yield

app = FastAPI(lifespan=lifespan)
app.mount("/static", StaticFiles(directory="static"), name="static")

# --- Pydantic Models for API Requests ---
class StartGameRequest(BaseModel):
    consent_given: bool; stats: Dict[str, int]
class ActionRequest(BaseModel):
    session_id: str; action_type: Literal["text", "button"]; value: str

# --- API Endpoints ---
@app.get("/", response_class=HTMLResponse)
async def read_root():
    # MODIFIED: Corrected path to "index.html"
    with open("index.html", "r", encoding="utf-8") as f:
        return HTMLResponse(content=f.read())

@app.post("/api/start_game")
async def start_game(req: StartGameRequest):
    if not req.consent_given:
        raise HTTPException(status_code=403, detail="Consent not given.")
    session_id = str(uuid.uuid4())
    session = RPGSession(
        user_id=session_id, session_id=session_id, stats=req.stats,
        story=[
            {"role": "system", "content": "You are a Dungeon Master for a one-shot RPG adventure."},
            {"role": "system", "content": f"The player's character stats are: { ' | '.join(f'{s}: {v:+}' for s, v in req.stats.items()) }"}
        ],
        state=RPGState.AWAITING_DESCRIPTION
    )
    active_sessions[session_id] = session
    session_last_access[session_id] = datetime.now(timezone.utc)
    return {"session_id": session_id, "message": "Character created! Please reply with a brief description of your character (name, appearance, backstory), or type 'skip'.", "state": "AWAITING_DESCRIPTION"}

@app.post("/api/game_action")
async def game_action(req: ActionRequest):
    if req.session_id not in active_sessions:
        raise HTTPException(status_code=404, detail="Session not found.")

    session = active_sessions[req.session_id]
    session_last_access[req.session_id] = datetime.now(timezone.utc)
    
    if session.state == RPGState.AWAITING_DESCRIPTION:
        if req.value.strip().lower() not in ['no', 'n', 'skip']:
            session.story.append({"role": "system", "content": f"Player description: \"{req.value}\""})
        session.dm_personality = system_prompt
        session.combat_module_enabled = True
        session.combat_stats = _calculate_combat_stats(session.stats)
        
        dungeon_master_prompt = "You are the Dungeon Master. Describe an immersive opening scene for the player. Introduce the environment and any NPCs. **Your response must NOT offer the player a list of choices or suggested actions.** You must conclude your narrative with only the open-ended question, 'What do you do now?'"
        
        llm_payload = session.story + [{"role": "system", "content": dungeon_master_prompt}]
        llm_payload = _add_dm_personality_to_payload(session, llm_payload)

        # --- MODIFIED: Store payload and signal client to listen ---
        session.pending_llm_payload = llm_payload
        return {"action": "listen_for_stream"}

    elif session.state in [RPGState.IDLE, RPGState.AWAITING_STAT_ACTION_INPUT]:
        action_text = req.value
        session.pending_action_text = action_text
        session.story.append({"role": "user", "content": action_text})

        stat_prompt