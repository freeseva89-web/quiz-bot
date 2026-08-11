import os
import re
import json
import time
import math
import random
import string
import asyncio
import logging
import html
from copy import deepcopy
from typing import Dict, List, Tuple, Optional, Any

import asyncpg
import redis.asyncio as aioredis
from aiohttp import web

from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Poll,
    InlineQueryResultArticle,
    InputTextMessageContent,
)
from telegram.error import TelegramError, TimedOut, NetworkError, RetryAfter
from telegram.request import HTTPXRequest
from telegram.ext import (
    Application,
    ApplicationBuilder,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    PollAnswerHandler,
    InlineQueryHandler,
    ContextTypes,
    filters,
)

# ==========================================
# 1. CONFIGURATION & ENVIRONMENT SETUP
# ==========================================
BOT_TOKEN = os.getenv("BOT_TOKEN", "YOUR_BOT_TOKEN_HERE")
BOT_USERNAME = ""  # Automatically detected in post_init
DATABASE_URL = os.getenv("DATABASE_URL", "postgresql://quizuser:password@localhost:5432/quizdb")
REDIS_URL = os.getenv("REDIS_URL", "redis://localhost:6379/0")

WEBHOOK_URL = os.getenv("WEBHOOK_URL", "")
PORT = int(os.getenv("PORT", "10000"))
WEBHOOK_SECRET = os.getenv("WEBHOOK_SECRET", "super_secret_webhook_token_123")

MAX_TELEGRAM_MSG_LEN = 3800
CORRECT_MARKS = ["*", "+"]

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO
)
logger = logging.getLogger("QuizBot")

db_pool: Optional[asyncpg.Pool] = None
redis_client: Optional[aioredis.Redis] = None
telegram_rate_limiter = asyncio.Semaphore(30)
background_tasks: set = set()

# --- HEALTH CHECK DUMMY SERVER FOR RENDER ---
async def handle_health(request):
    return web.Response(text="Quiz Bot Web Engine Active")

async def start_dummy_server():
    app = web.Application()
    app.router.add_get('/', handle_health)
    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, '0.0.0.0', PORT)
    await site.start()
    logger.info(f"✅ Render Dummy Web Server running on port {PORT}")

# ==========================================
# 2. UTILITY & HELPERS
# ==========================================
def generate_short_code(length: int = 8) -> str:
    chars = string.ascii_uppercase + string.digits
    return "".join(random.choice(chars) for _ in range(length))

def count_correct_marks(text: str) -> int:
    text_lower = text.lower()
    return sum(text_lower.count(mark) for mark in CORRECT_MARKS)

def remove_correct_marks(text: str) -> str:
    clean_text = text
    for mark in CORRECT_MARKS:
        pattern = re.compile(re.escape(mark), re.IGNORECASE)
        clean_text = pattern.sub("", clean_text)
    return re.sub(r"\s+", " ", clean_text).strip()

def get_progress_bar(score: int, total: int) -> str:
    if total <= 0:
        return "▱▱▱▱▱▱▱▱▱▱"
    percentage = (score / total) * 100
    filled = int(round(percentage / 10))
    return "▰" * filled + "▱" * (10 - filled)

def track_task(task: asyncio.Task) -> None:
    background_tasks.add(task)
    task.add_done_callback(background_tasks.discard)

async def check_admin_or_owner(chat, user_id: int, owner_id: str) -> bool:
    if chat.type in ["private"]:
        return True
    
    # 1. Check if user is Quiz Creator/Host
    if owner_id and str(user_id) == str(owner_id):
        return True

    # 2. Check Telegram Group Admin Permissions
    try:
        chat_member = await chat.get_member(user_id)
        if chat_member.status in ['creator', 'administrator']:
            return True
    except TelegramError as e:
        logger.error(f"Error checking admin status: {e}")
        
    return False

# ==========================================
# 3. DATABASE & REDIS INFRASTRUCTURE
# ==========================================
async def init_infrastructure():
    global db_pool, redis_client
    try:
        db_pool = await asyncpg.create_pool(
            dsn=DATABASE_URL,
            min_size=5,
            max_size=25,
            command_timeout=30.0
        )
        logger.info("✅ PostgreSQL Connection Pool Initialized.")
        
        async with db_pool.acquire() as conn:
            await conn.execute("""
                CREATE TABLE IF NOT EXISTS quizzes (
                    id SERIAL PRIMARY KEY,
                    short_code VARCHAR(12) UNIQUE NOT NULL,
                    owner_id BIGINT NOT NULL,
                    title TEXT NOT NULL,
                    questions JSONB NOT NULL,
                    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
                );

                CREATE INDEX IF NOT EXISTS idx_quizzes_owner_id ON quizzes(owner_id);
                CREATE INDEX IF NOT EXISTS idx_quizzes_short_code ON quizzes(short_code);

                CREATE TABLE IF NOT EXISTS quiz_results (
                    id SERIAL PRIMARY KEY,
                    quiz_id INT REFERENCES quizzes(id) ON DELETE CASCADE,
                    chat_id BIGINT NOT NULL,
                    user_id BIGINT NOT NULL,
                    user_name TEXT,
                    score INT NOT NULL,
                    total_time DOUBLE PRECISION NOT NULL,
                    completed_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
                );

                CREATE INDEX IF NOT EXISTS idx_quiz_results_quiz_chat ON quiz_results(quiz_id, chat_id);
            """)
        logger.info("✅ PostgreSQL Database Tables & Indexes Verified.")
    except Exception as e:
        logger.critical(f"❌ PostgreSQL Initialization Failed: {e}")
        raise e

    try:
        redis_client = aioredis.from_url(
            REDIS_URL,
            decode_responses=True,
            max_connections=50,
            socket_timeout=5.0,
            socket_connect_timeout=5.0
        )
        await redis_client.ping()
        logger.info("✅ Redis Connection Initialized.")
    except Exception as e:
        logger.critical(f"❌ Redis Initialization Failed: {e}")
        raise e

async def save_quiz_async(owner_id: int, title: str, questions: list) -> Tuple[int, str]:
    if not db_pool:
        raise Exception("Database Pool connection is missing.")
    short_code = generate_short_code()
    async with db_pool.acquire() as conn:
        row = await conn.fetchrow(
            """
            INSERT INTO quizzes (short_code, owner_id, title, questions)
            VALUES ($1, $2, $3, $4::jsonb)
            RETURNING id, short_code
            """,
            short_code, owner_id, title, json.dumps(questions, ensure_ascii=False)
        )
        return row['id'], row['short_code']

async def get_my_quizzes_async(owner_id: int) -> List[asyncpg.Record]:
    if not db_pool:
        return []
    async with db_pool.acquire() as conn:
        return await conn.fetch(
            "SELECT id, short_code, title, created_at FROM quizzes WHERE owner_id=$1 ORDER BY id DESC LIMIT 50",
            owner_id
        )

async def load_quiz_by_code_or_id(identifier: str):
    if not db_pool:
        return None
    async with db_pool.acquire() as conn:
        if identifier.isdigit():
            row = await conn.fetchrow(
                "SELECT owner_id, title, questions, short_code, id FROM quizzes WHERE id=$1 OR short_code=$2",
                int(identifier), identifier
            )
        else:
            row = await conn.fetchrow(
                "SELECT owner_id, title, questions, short_code, id FROM quizzes WHERE short_code=$1",
                identifier
            )
            
        if row:
            questions = json.loads(row['questions']) if isinstance(row['questions'], str) else row['questions']
            return row['owner_id'], row['title'], questions, row['short_code'], row['id']
    return None

async def delete_quiz_async(owner_id: int, quiz_id: int) -> bool:
    if not db_pool:
        return False
    async with db_pool.acquire() as conn:
        res = await conn.execute("DELETE FROM quizzes WHERE id=$1 AND owner_id=$2", quiz_id, owner_id)
        return res != "DELETE 0"

# ==========================================
# 4. PARSER & UI BUILDERS
# ==========================================
def parse_questions_flexible(text: str):
    lines = text.splitlines()
    raw_blocks, current_block = [], []

    question_pattern = re.compile(
        r"^\s*(?:(?:प्रश्न|Question|Q)\s*\d*|\d+)\s*[\.\):\-]\s*(.+?)\s*$",
        re.IGNORECASE
    )

    for line in lines:
        if not line.strip():
            continue
        if question_pattern.match(line.strip()):
            if current_block:
                raw_blocks.append(current_block)
                current_block = []
        current_block.append(line.strip())

    if current_block:
        raw_blocks.append(current_block)

    option_pattern = re.compile(r"^\s*([A-Da-d0-9])\s*[\.\):\-]\s*(.+?)\s*$")
    valid_questions = []
    skipped_count = 0

    for block in raw_blocks:
        options, correct_candidates = [], []
        explanation = ""
        correct_mark_count = 0

        q_match = question_pattern.match(block[0])
        q_text = q_match.group(1).strip() if q_match else block[0]

        for line in block[1:]:
            opt_match = option_pattern.match(line)
            if opt_match:
                raw_opt = opt_match.group(2).strip()
                marks = count_correct_marks(raw_opt)
                opt_clean = remove_correct_marks(raw_opt)
                options.append(opt_clean)

                if marks > 0:
                    correct_mark_count += marks
                    correct_candidates.append(len(options) - 1)
            else:
                lower = line.lower()
                if lower.startswith("explanation:") or line.startswith("व्याख्या:"):
                    explanation = line.split(":", 1)[1].strip()

        if (
            q_text
            and len(q_text) <= 300
            and 2 <= len(options) <= 10
            and correct_mark_count == 1
            and len(correct_candidates) == 1
            and all(len(o) <= 100 for o in options)
            and len(explanation) <= 200
        ):
            valid_questions.append({
                "question": q_text,
                "options": options,
                "correct": correct_candidates[0],
                "explanation": explanation
            })
        else:
            skipped_count += 1

    return valid_questions, skipped_count

def build_settings_keyboard(data: dict) -> InlineKeyboardMarkup:
    q_shuffle = "ON" if data.get("qshuffle") else "OFF"
    o_shuffle = "ON" if data.get("oshuffle") else "OFF"
    explanation = "ON" if data.get("explanation") else "OFF"
    timer = data.get("timer", 20)
    short_code = data.get("short_code", "")

    keyboard = [[InlineKeyboardButton("▶️ Start Quiz", callback_data="start_quiz")]]

    if short_code:
        share_url = f"https://t.me/share/url?url=https://t.me/{BOT_USERNAME}?start=quiz_{short_code}"
        group_url = f"https://t.me/{BOT_USERNAME}?startgroup=quiz_{short_code}"
        keyboard.append([InlineKeyboardButton("➕ Start in Group", url=group_url)])
        keyboard.append([InlineKeyboardButton("📲 Share Quiz", url=share_url)])

    keyboard.extend([
        [
            InlineKeyboardButton(f"🔀 Qs: {q_shuffle}", callback_data="toggle_qshuffle"),
            InlineKeyboardButton(f"🔀 Opts: {o_shuffle}", callback_data="toggle_oshuffle")
        ],
        [InlineKeyboardButton(f"💡 Exp: {explanation}", callback_data="toggle_exp")],
        [
            InlineKeyboardButton(f"{'🔘 ' if timer == 10 else ''}10s", callback_data="set_timer_10"),
            InlineKeyboardButton(f"{'🔘 ' if timer == 20 else ''}20s", callback_data="set_timer_20"),
            InlineKeyboardButton(f"{'🔘 ' if timer == 30 else ''}30s", callback_data="set_timer_30")
        ],
        [
            InlineKeyboardButton(f"{'🔘 ' if timer == 45 else ''}45s", callback_data="set_timer_45"),
            InlineKeyboardButton(f"{'🔘 ' if timer == 60 else ''}60s", callback_data="set_timer_60")
        ]
    ])

    return InlineKeyboardMarkup(keyboard)

# ==========================================
# 5. TELEGRAM COMMAND HANDLERS
# ==========================================
async def start_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if context.args:
        arg = context.args[0]
        code = arg.replace("quiz_", "")
        loaded = await load_quiz_by_code_or_id(code)

        if loaded:
            owner_id, title, questions, short_code, quiz_id = loaded
            context.user_data.update({
                "owner_id": owner_id,
                "quiz_id": quiz_id,
                "short_code": short_code,
                "quiz_title": title,
                "questions": questions,
                "qshuffle": context.user_data.get("qshuffle", False),
                "oshuffle": context.user_data.get("oshuffle", False),
                "explanation": context.user_data.get("explanation", True),
                "timer": context.user_data.get("timer", 20)
            })

            if update.effective_chat.type in ["group", "supergroup"]:
                await begin_quiz(update.effective_chat.id, context)
                return

            share_link = f"https://t.me/{BOT_USERNAME}?start=quiz_{short_code}"
            await update.message.reply_text(
                f"👍 Loaded: <b>{html.escape(title)}</b>\n"
                f"📋 Questions: {len(questions)}\n\n"
                f"Share Link:\n<code>{share_link}</code>",
                parse_mode="HTML",
                reply_markup=build_settings_keyboard(context.user_data)
            )
            return

    keyboard = [
        [InlineKeyboardButton("📝 Create Quiz", callback_data="create")],
        [InlineKeyboardButton("📚 My Quizzes", callback_data="my_quizzes")],
        [InlineKeyboardButton("❓ Help", callback_data="help")]
    ]

    await update.message.reply_text(
        "🤖 <b>ENTERPRISE HIGH-SCALE QUIZ BOT</b>\n\nSelect an option below:",
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup(keyboard)
    )

async def inline_query_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.inline_query.query.strip()
    if not query:
        return

    code = query.replace("quiz_", "")
    loaded = await load_quiz_by_code_or_id(code)

    results = []
    if loaded:
        _, title, questions, short_code, _ = loaded
        start_link = f"https://t.me/{BOT_USERNAME}?start=quiz_{short_code}"
        
        results.append(
            InlineQueryResultArticle(
                id=short_code,
                title=f"📝 Start Quiz: {title}",
                description=f"Questions: {len(questions)}",
                input_message_content=InputTextMessageContent(
                    f"<b>{html.escape(title)}</b>\n\n📋 Questions: {len(questions)}",
                    parse_mode="HTML"
                ),
                reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("▶️ Start Quiz", url=start_link)]])
            )
        )
    await update.inline_query.answer(results, cache_time=0)

async def create_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.type != "private":
        return
    context.user_data.clear()
    context.user_data["owner_id"] = update.effective_user.id
    context.user_data["waiting_title"] = True
    context.user_data["temp_questions"] = []
    await update.message.reply_text("Send Me Your Quiz Title", parse_mode="HTML")

async def done_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.type != "private":
        return

    questions = context.user_data.get("temp_questions", [])
    title = context.user_data.get("quiz_title", "Untitled Quiz")

    if not questions:
        await update.message.reply_text("❌ No questions added.")
        return

    user_id = update.effective_user.id
    try:
        quiz_id, short_code = await save_quiz_async(user_id, title, questions)
    except Exception:
        await update.message.reply_text("❌ Failed to save quiz. Try again later.")
        return

    context.user_data["waiting_questions"] = False
    context.user_data["temp_questions"] = []
    context.user_data.update({
        "quiz_id": quiz_id,
        "short_code": short_code,
        "questions": questions,
        "qshuffle": False,
        "oshuffle": False,
        "explanation": True,
        "timer": 20
    })

    share_link = f"https://t.me/{BOT_USERNAME}?start=quiz_{short_code}"

    await update.message.reply_text(
        f"✅ <b>Quiz Created Successfully!</b>\n\n"
        f"📌 Title: <b>{html.escape(title)}</b>\n"
        f"📋 Questions: {len(questions)}\n\n"
        f"Share Link:\n<code>{share_link}</code>",
        parse_mode="HTML",
        reply_markup=build_settings_keyboard(context.user_data)
    )

# --- STRICT CONTROL HANDLERS (STOP/PAUSE & CANCEL) ---
async def stop_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    user = update.effective_user
    chat_key = str(chat.id)

    is_active = await redis_client.get(f"quiz_active:{chat_key}")
    if not is_active:
        await update.message.reply_text("❌ No active quiz running in this chat.")
        return

    owner_id = await redis_client.hget(f"quiz_state:{chat_key}", "owner_id")
    is_authorized = await check_admin_or_owner(chat, user.id, owner_id)

    if not is_authorized:
        await update.message.reply_text("⚠️ Permission Denied! Only Group Admins or Quiz Host can pause the quiz.")
        return

    await redis_client.set(f"quiz_pause:{chat_key}", "1", ex=86400)
    
    keyboard = InlineKeyboardMarkup([
        [InlineKeyboardButton("▶️ Resume Quiz", callback_data=f"resume_quiz_{chat_key}")]
    ])
    await update.message.reply_text(
        "⏸️ <b>Quiz Pause Ho Gaya Hai.</b>\nDobara start karne ke liye niche button par click karein:",
        parse_mode="HTML",
        reply_markup=keyboard
    )

async def cancel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    user = update.effective_user
    chat_key = str(chat.id)

    is_active = await redis_client.get(f"quiz_active:{chat_key}")
    if not is_active:
        await update.message.reply_text("❌ No active quiz running in this chat.")
        return

    owner_id = await redis_client.hget(f"quiz_state:{chat_key}", "owner_id")
    is_authorized = await check_admin_or_owner(chat, user.id, owner_id)

    if not is_authorized:
        await update.message.reply_text("⚠️ Permission Denied! Only Group Admins or Quiz Host can cancel the quiz.")
        return

    await redis_client.set(f"quiz_stop:{chat_key}", "1", ex=3600)
    await redis_client.delete(f"quiz_pause:{chat_key}")
    await update.message.reply_text("🛑 Stopping and cancelling the quiz completely...")

async def force_reset_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat = update.effective_chat
    user = update.effective_user
    chat_key = str(chat.id)

    owner_id = await redis_client.hget(f"quiz_state:{chat_key}", "owner_id")
    is_authorized = await check_admin_or_owner(chat, user.id, owner_id)

    if not is_authorized:
        await update.message.reply_text("⚠️ Permission Denied! Only Group Admins or Quiz Host can reset the quiz.")
        return

    await redis_client.delete(
        f"quiz_active:{chat_key}",
        f"quiz_state:{chat_key}",
        f"quiz_stop:{chat_key}",
        f"quiz_pause:{chat_key}",
        f"quiz_next:{chat_key}",
        f"participants:{chat_key}",
        f"scores:{chat_key}",
        f"times:{chat_key}",
        f"leaderboard:{chat_key}"
    )
    await update.message.reply_text("🧹 <b>Quiz state completely reset!</b> You can start a new quiz now.", parse_mode="HTML")

async def resume_quiz_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    chat = query.message.chat
    user = query.from_user
    chat_key = str(chat.id)

    is_paused = await redis_client.get(f"quiz_pause:{chat_key}")
    if not is_paused:
        await query.answer("❌ No paused quiz found.", show_alert=True)
        return

    owner_id = await redis_client.hget(f"quiz_state:{chat_key}", "owner_id")
    is_authorized = await check_admin_or_owner(chat, user.id, owner_id)

    if not is_authorized:
        await query.answer("⚠️ Sirf Admin ya Quiz Host hi quiz resume kar sakta hai!", show_alert=True)
        return

    await redis_client.delete(f"quiz_pause:{chat_key}")
    await query.answer("▶️ Resuming Quiz...")
    await query.edit_message_text("▶️ <b>Quiz wahin se dobara start ho raha hai...</b>", parse_mode="HTML")

async def show_my_quizzes(query_or_update, context):
    user_id = query_or_update.from_user.id if hasattr(query_or_update, "from_user") else query_or_update.effective_user.id
    quizzes = await get_my_quizzes_async(user_id)

    if not quizzes:
        msg = "📚 No saved quizzes found."
        if hasattr(query_or_update, "edit_message_text"):
            await query_or_update.edit_message_text(msg, parse_mode="HTML")
        else:
            await query_or_update.message.reply_text(msg, parse_mode="HTML")
        return

    buttons = []
    for row in quizzes[:15]:
        buttons.append([
            InlineKeyboardButton(f"▶️ {row['title']}", callback_data=f"load_{row['short_code']}"),
            InlineKeyboardButton("🗑 Delete", callback_data=f"del_{row['id']}")
        ])

    buttons.append([InlineKeyboardButton("⬅️ Back", callback_data="back_start")])
    
    markup = InlineKeyboardMarkup(buttons)
    if hasattr(query_or_update, "edit_message_text"):
        await query_or_update.edit_message_text("📚 <b>MY QUIZZES</b>", parse_mode="HTML", reply_markup=markup)
    else:
        await query_or_update.message.reply_text("📚 <b>MY QUIZZES</b>", parse_mode="HTML", reply_markup=markup)

async def button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    data = query.data

    if data.startswith("resume_quiz_"):
        await resume_quiz_callback(update, context)
        return

    if data == "create":
        if query.message.chat.type != "private":
            await query.answer("Please use private chat.", show_alert=True)
            return
        await query.answer()
        context.user_data.clear()
        context.user_data["owner_id"] = query.from_user.id
        context.user_data["waiting_title"] = True
        context.user_data["temp_questions"] = []
        await query.edit_message_text("Send Me Your Quiz Title", parse_mode="HTML")
        return

    if data == "my_quizzes":
        await query.answer()
        await show_my_quizzes(query, context)
        return

    if data == "help":
        await query.answer()
        await query.edit_message_text("📖 <b>HELP</b>\n\nMark * Or + Against The Correct Option", parse_mode="HTML")
        return

    if data == "back_start":
        await query.answer()
        keyboard = [
            [InlineKeyboardButton("📝 Create Quiz", callback_data="create")],
            [InlineKeyboardButton("📚 My Quizzes", callback_data="my_quizzes")],
            [InlineKeyboardButton("❓ Help", callback_data="help")]
        ]
        await query.edit_message_text("🤖 <b>ENTERPRISE HIGH-SCALE QUIZ BOT</b>", parse_mode="HTML", reply_markup=InlineKeyboardMarkup(keyboard))
        return

    if data.startswith("del_"):
        quiz_id = int(data.split("_")[1])
        deleted = await delete_quiz_async(query.from_user.id, quiz_id)
        if deleted:
            await query.answer("🗑 Quiz Deleted!", show_alert=True)
            await show_my_quizzes(query, context)
        else:
            await query.answer("❌ Failed to delete.", show_alert=True)
        return

    if data.startswith("load_"):
        code = data.split("_", 1)[1]
        loaded = await load_quiz_by_code_or_id(code)
        if not loaded:
            await query.answer("❌ Quiz not found.", show_alert=True)
            return

        owner_id, title, questions, short_code, quiz_id = loaded
        await query.answer()
        context.user_data.clear()
        context.user_data.update({
            "owner_id": query.from_user.id,
            "quiz_id": quiz_id,
            "short_code": short_code,
            "quiz_title": title,
            "questions": questions,
            "qshuffle": False,
            "oshuffle": False,
            "explanation": True,
            "timer": 20
        })

        share_link = f"https://t.me/{BOT_USERNAME}?start=quiz_{short_code}"
        await query.edit_message_text(
            f"👍 Loaded: <b>{html.escape(title)}</b>\n"
            f"📋 Questions: {len(questions)}\n\n"
            f"Share Link:\n<code>{share_link}</code>",
            parse_mode="HTML",
            reply_markup=build_settings_keyboard(context.user_data)
        )
        return

    if data == "toggle_qshuffle":
        context.user_data["qshuffle"] = not context.user_data.get("qshuffle", False)
        await query.answer()
    elif data == "toggle_oshuffle":
        context.user_data["oshuffle"] = not context.user_data.get("oshuffle", False)
        await query.answer()
    elif data == "toggle_exp":
        context.user_data["explanation"] = not context.user_data.get("explanation", True)
        await query.answer()
    elif data.startswith("set_timer_"):
        timer_val = int(data.split("_")[-1])
        context.user_data["timer"] = timer_val
        await query.answer(f"Timer set to {timer_val}s")
    elif data == "start_quiz":
        await query.answer()
        await begin_quiz(query.message.chat_id, context)
        return

    try:
        await query.edit_message_reply_markup(reply_markup=build_settings_keyboard(context.user_data))
    except TelegramError:
        pass

async def receive_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.type != "private":
        return

    if context.user_data.get("waiting_title"):
        title = update.message.text.strip()
        if not title or len(title) > 200:
            await update.message.reply_text("❌ Title cannot be empty or longer than 200 chars.")
            return

        context.user_data["quiz_title"] = title
        context.user_data["waiting_title"] = False
        context.user_data["waiting_questions"] = True
        context.user_data["temp_questions"] = []

        await update.message.reply_text("Send Question Text Format.\nMark * Or + Against Correct Option.", parse_mode="HTML")
        return

    if context.user_data.get("waiting_questions"):
        text = update.message.text
        questions, skipped = parse_questions_flexible(text)

        if not questions:
            await update.message.reply_text("❌ Valid question format not found.")
            return

        current_list = context.user_data.get("temp_questions", [])
        if len(current_list) + len(questions) > 1000:
            await update.message.reply_text("⚠️ Maximum limit is 1000 questions per quiz.")
            return

        current_list.extend(questions)
        context.user_data["temp_questions"] = current_list

        skip_msg = f"\n⚠️ Skipped {skipped} invalid items." if skipped > 0 else ""
        done_keyboard = InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ Done Adding Questions", callback_data="finish_creation")],
            [InlineKeyboardButton("❌ Cancel", callback_data="cancel_creation")]
        ])

        await update.message.reply_text(
            f"✅ <b>{len(questions)} Questions Added!</b>{skip_msg}\n"
            f"📊 Total So Far: {len(current_list)}\n\n"
            f"Send more OR click /done when finished.",
            parse_mode="HTML",
            reply_markup=done_keyboard
        )

async def creation_button_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    if query.data == "finish_creation":
        await query.answer()
        await done_command(update, context)
    elif query.data == "cancel_creation":
        await query.answer()
        context.user_data.clear()
        await query.edit_message_text("❌ Quiz creation cancelled.")

# ==========================================
# 6. HIGH-CONCURRENCY QUIZ ENGINE & LOOPS
# ==========================================
async def begin_quiz(chat_id: int, context: ContextTypes.DEFAULT_TYPE):
    chat_key = str(chat_id)
    
    lock = redis_client.lock(f"lock:quiz_start:{chat_key}", timeout=10)
    acquired = await lock.acquire(blocking=False)
    if not acquired:
        await context.bot.send_message(chat_id, "⚠️ Quiz initialization in progress...")
        return

    try:
        active = await redis_client.get(f"quiz_active:{chat_key}")
        if active:
            await context.bot.send_message(chat_id, "⚠️ A quiz is already running in this chat.")
            return

        questions = deepcopy(context.user_data.get("questions", []))
        if not questions:
            await context.bot.send_message(chat_id, "❌ No questions found in quiz.")
            return

        qshuffle = context.user_data.get("qshuffle", False)
        oshuffle = context.user_data.get("oshuffle", False)
        explanation_enable = context.user_data.get("explanation", True)
        timer = context.user_data.get("timer", 20)
        title = context.user_data.get("quiz_title", "Quiz")
        owner_id = context.user_data.get("owner_id", 0)
        quiz_id = context.user_data.get("quiz_id", 0)

        if qshuffle:
            random.shuffle(questions)

        is_private = (chat_id > 0)

        await redis_client.set(f"quiz_active:{chat_key}", "1", ex=86400)
        await redis_client.hset(f"quiz_state:{chat_key}", mapping={
            "owner_id": owner_id,
            "quiz_id": quiz_id,
            "title": title,
            "timer": timer,
            "is_private": "1" if is_private else "0",
            "total_q": len(questions)
        })

        await context.bot.send_message(
            chat_id,
            f"🚀 <b>Quiz starting in 5 seconds...</b>\n\n"
            f"📚 Title: <b>{html.escape(title)}</b>\n"
            f"📋 Questions: {len(questions)}\n"
            f"⏱ Timer: {timer}s",
            parse_mode="HTML"
        )

        await asyncio.sleep(5)
        
        task = asyncio.create_task(
            run_quiz_loop(
                chat_key=chat_key,
                chat_id=chat_id,
                questions=questions,
                context=context,
                oshuffle=oshuffle,
                explanation_enable=explanation_enable,
                timer=timer
            )
        )
        track_task(task)

    finally:
        try:
            await lock.release()
        except Exception:
            pass

async def send_poll_with_rate_limit(context, chat_id, question, options, correct_index, explanation, timer, retries=3):
    async with telegram_rate_limiter:
        await asyncio.sleep(0.04)
        for attempt in range(retries):
            try:
                return await context.bot.send_poll(
                    chat_id=chat_id,
                    question=question,
                    options=options,
                    type=Poll.QUIZ,
                    correct_option_id=correct_index,
                    explanation=explanation,
                    open_period=int(timer),
                    is_anonymous=False
                )
            except RetryAfter as e:
                await asyncio.sleep(e.retry_after + 0.5)
            except (TimedOut, NetworkError):
                if attempt < retries - 1:
                    await asyncio.sleep(2)
                else:
                    raise
            except TelegramError:
                raise

async def run_quiz_loop(chat_key: str, chat_id: int, questions: list, context: ContextTypes.DEFAULT_TYPE, oshuffle: bool, explanation_enable: bool, timer: int):
    total_questions = len(questions)

    try:
        index = 1
        while index <= total_questions:
            # Check if cancelled or stopped
            if await redis_client.get(f"quiz_stop:{chat_key}"):
                break

            # Check if paused (Wait gracefully without CPU spiking)
            while await redis_client.get(f"quiz_pause:{chat_key}"):
                await asyncio.sleep(1)
                if await redis_client.get(f"quiz_stop:{chat_key}"):
                    break

            if await redis_client.get(f"quiz_stop:{chat_key}"):
                break

            q = questions[index - 1]
            options = list(q["options"])
            correct_index = q["correct"]

            if oshuffle:
                indexed = list(enumerate(options))
                random.shuffle(indexed)
                options = [opt for _, opt in indexed]
                correct_index = next(
                    n for n, (original_index, _) in enumerate(indexed)
                    if original_index == q["correct"]
                )

            explanation = q.get("explanation") if explanation_enable else None

            try:
                poll_msg = await send_poll_with_rate_limit(
                    context,
                    chat_id,
                    f"[{index}/{total_questions}] {q['question']}",
                    options,
                    correct_index,
                    explanation,
                    timer
                )
            except Exception:
                logger.exception("Poll delivery error in loop.")
                await context.bot.send_message(chat_id, "❌ Poll delivery failed due to rate limits or connection loss.")
                break

            poll_id = poll_msg.poll.id
            q_start_time = time.time()

            await redis_client.set(
                f"poll_mapping:{poll_id}",
                json.dumps({"chat_key": chat_key, "correct": correct_index, "start_time": q_start_time}),
                ex=86400
            )

            is_private = (chat_id > 0)
            wait_time = 0.0
            
            # --- TIMER & FAST SKIP CONTROL LOGIC ---
            while wait_time < timer:
                if await redis_client.get(f"quiz_stop:{chat_key}") or await redis_client.get(f"quiz_pause:{chat_key}"):
                    break
                
                # Private chat mein answer click hone par 1 second safe delay leke skip karega
                if is_private and await redis_client.get(f"quiz_next:{chat_key}"):
                    await redis_client.delete(f"quiz_next:{chat_key}")
                    await asyncio.sleep(1.0) # Graceful 1s buffer delay
                    break
                
                await asyncio.sleep(0.5)
                wait_time += 0.5

            index += 1
            await asyncio.sleep(1.0)
    finally:
        await finish_quiz(chat_key, context, chat_id=chat_id)

async def poll_answer_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    answer = update.poll_answer
    poll_id = answer.poll_id
    user = answer.user

    if not user:
        return

    raw_poll_data = await redis_client.get(f"poll_mapping:{poll_id}")
    if not raw_poll_data:
        return

    pdata = json.loads(raw_poll_data)
    chat_key = pdata["chat_key"]
    correct_option = pdata["correct"]
    q_start_time = pdata["start_time"]

    first_answer = await redis_client.set(f"answered:{poll_id}:{user.id}", "1", nx=True, ex=7200)
    if not first_answer:
        return

    time_taken = max(0.1, time.time() - q_start_time)
    user_name = user.full_name

    await redis_client.hset(f"participants:{chat_key}", str(user.id), user_name)

    if answer.option_ids and answer.option_ids[0] == correct_option:
        await redis_client.hincrby(f"scores:{chat_key}", str(user.id), 1)

    await redis_client.hincrbyfloat(f"times:{chat_key}", str(user.id), time_taken)

    score = int(await redis_client.hget(f"scores:{chat_key}", str(user.id)) or 0)
    total_time = float(await redis_client.hget(f"times:{chat_key}", str(user.id)) or 0.0)

    composite_rank = (score * 1000000) - min(total_time, 999999.0)
    await redis_client.zadd(f"leaderboard:{chat_key}", {str(user.id): composite_rank})

    # Trigger fast-skip in private chat
    chat_id = int(chat_key)
    if chat_id > 0:
        await redis_client.set(f"quiz_next:{chat_key}", "1", ex=60)

async def finish_quiz(chat_key: str, context: ContextTypes.DEFAULT_TYPE, chat_id: int = None):
    lock = redis_client.lock(f"lock:finish:{chat_key}", timeout=30)
    acquired = await lock.acquire(blocking=False)
    if not acquired:
        return

    try:
        target_chat_id = chat_id if chat_id is not None else int(chat_key)
        stopped = await redis_client.get(f"quiz_stop:{chat_key}")

        quiz_info = await redis_client.hgetall(f"quiz_state:{chat_key}")
        title = quiz_info.get("title", "Quiz")
        total_q = int(quiz_info.get("total_q", 0))

        participants = await redis_client.hgetall(f"participants:{chat_key}")
        scores = await redis_client.hgetall(f"scores:{chat_key}")
        times = await redis_client.hgetall(f"times:{chat_key}")

        total_candidates = len(participants)

        if total_candidates == 0:
            msg = f"🏆 <b>{html.escape(title)}</b>\n\nNobody participated in this quiz."
            try:
                await context.bot.send_message(target_chat_id, msg, parse_mode="HTML")
            except TelegramError:
                pass
        else:
            ranked_users = await redis_client.zrevrange(f"leaderboard:{chat_key}", 0, -1, withscores=False)
            
            leaderboard = []
            for uid in ranked_users:
                name = participants.get(uid, "User")
                sc = int(scores.get(uid, 0))
                tm = float(times.get(uid, 0.0))
                leaderboard.append((int(uid), name, sc, tm))

            # Database me score store hone ka wait karenge tabhi Redis clear karenge
            await persist_results_to_db(chat_key, leaderboard)

            avg_time = sum(t for _, _, _, t in leaderboard) / total_candidates
            real_topper = leaderboard[0]
            class_avg_score = sum(s for _, _, s, _ in leaderboard) / total_candidates

            header_title = "🛑 QUIZ STOPPED REPORT" if stopped else "🏆 QUIZ RESULT DASHBOARD"

            header = (
                "┌──────────────────────────────────────┐\n"
                f"│       {header_title}       │\n"
                "└──────────────────────────────────────┘\n"
                f"📌 Title : <b>{html.escape(title)}</b>\n"
                f"👥 Total : {total_candidates} Candidates\n"
                f"⏱ Avg Time : {avg_time:.1f}s\n"
                "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n\n"
            )

            medals = ["🥇", "🥈", "🥉"]
            chunk = header

            for rank, (uid, name, score, t_secs) in enumerate(leaderboard, start=1):
                beaten = total_candidates - rank
                pct = (score / total_q * 100) if total_q > 0 else 0
                pbar = get_progress_bar(score, total_q)

                if total_candidates > 1:
                    percentile = (beaten / (total_candidates - 1)) * 100
                    status_str = f"Ahead of {beaten} Candidates ({percentile:.1f}%)"
                else:
                    status_str = "Top Performer"

                if rank <= 3:
                    badge = medals[rank - 1]
                    line = (
                        f"{badge} <b>{html.escape(name)}</b>\n"
                        f"   📊 Score: {score}/{total_q}  {pbar} {pct:.0f}%\n"
                        f"   🕓 Time: {t_secs:.1f}s\n"
                        f"   🎯 Status: {status_str}\n\n"
                    )
                else:
                    line = (
                        f"<b>{rank}. {html.escape(name)}</b>\n"
                        f"   • {score}/{total_q} Marks ({pct:.0f}%) | Time: {t_secs:.1f}s\n\n"
                    )

                if len(chunk) + len(line) > MAX_TELEGRAM_MSG_LEN:
                    try:
                        await context.bot.send_message(target_chat_id, chunk, parse_mode="HTML")
                    except TelegramError:
                        pass
                    chunk = line
                else:
                    chunk += line

            footer = (
                "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                f"• Class Average : {class_avg_score:.1f} / {total_q}\n"
                f"• Top Ranker ⚡: <b>{html.escape(real_topper[1])}</b> ({real_topper[3]:.1f}s)\n"
                "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
            )

            if len(chunk) + len(footer) > MAX_TELEGRAM_MSG_LEN:
                try:
                    await context.bot.send_message(target_chat_id, chunk, parse_mode="HTML")
                except TelegramError:
                    pass
                chunk = footer
            else:
                chunk += footer

            try:
                await context.bot.send_message(target_chat_id, chunk, parse_mode="HTML")
            except TelegramError:
                pass

        await redis_client.delete(
            f"quiz_active:{chat_key}",
            f"quiz_state:{chat_key}",
            f"quiz_stop:{chat_key}",
            f"quiz_pause:{chat_key}",
            f"quiz_next:{chat_key}",
            f"participants:{chat_key}",
            f"scores:{chat_key}",
            f"times:{chat_key}",
            f"leaderboard:{chat_key}"
        )

    finally:
        try:
            await lock.release()
        except Exception:
            pass

async def persist_results_to_db(chat_key: str, leaderboard: list):
    if not db_pool:
        return
    try:
        chat_id = int(chat_key)
        quiz_info = await redis_client.hgetall(f"quiz_state:{chat_key}")
        quiz_id = int(quiz_info.get("quiz_id") or 0)
        
        quiz_id_val = quiz_id if quiz_id > 0 else None

        async with db_pool.acquire() as conn:
            async with conn.transaction():
                for uid, name, score, t_secs in leaderboard:
                    await conn.execute(
                        """
                        INSERT INTO quiz_results (quiz_id, chat_id, user_id, user_name, score, total_time)
                        VALUES ($1, $2, $3, $4, $5, $6)
                        """,
                        quiz_id_val, chat_id, uid, name, score, t_secs
                    )
        logger.info(f"✅ Quiz results persisted to DB for chat {chat_key}")
    except Exception as e:
        logger.error(f"❌ DB Batch Persistence Error: {e}")

# ==========================================
# 7. LIFECYCLE & MAIN EXECUTION
# ==========================================
async def post_init(application: Application):
    global BOT_USERNAME
    bot_info = await application.bot.get_me()
    BOT_USERNAME = bot_info.username
    logger.info(f"🤖 Bot Username Automatically Detected: @{BOT_USERNAME}")

    await start_dummy_server()
    await init_infrastructure()
    
    if WEBHOOK_URL:
        webhook_endpoint = f"{WEBHOOK_URL}/telegram/{BOT_TOKEN}"
        await application.bot.set_webhook(
            url=webhook_endpoint,
            secret_token=WEBHOOK_SECRET,
            allowed_updates=["message", "callback_query", "poll_answer", "inline_query"]
        )
        logger.info(f"✅ Webhook configured on {webhook_endpoint}")

async def post_shutdown(application: Application):
    logger.info("🛑 Executing Graceful Application Shutdown...")
    
    for task in background_tasks:
        task.cancel()
    await asyncio.gather(*background_tasks, return_exceptions=True)

    if redis_client:
        await redis_client.close()
    if db_pool:
        await db_pool.close()
    logger.info("✅ All connections safely closed.")

def main():
    request = HTTPXRequest(connect_timeout=30.0, read_timeout=30.0)
    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .request(request)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    app.add_handler(CommandHandler(["start"], start_handler))
    app.add_handler(CommandHandler(["create", "newquiz"], create_command))
    app.add_handler(CommandHandler(["done"], done_command))
    
    app.add_handler(CommandHandler(["stop", "endquiz", "pause"], stop_command))
    app.add_handler(CommandHandler(["cancel", "stopquiz", "kill"], cancel_command))
    app.add_handler(CommandHandler(["resetquiz", "clearquiz", "reset"], force_reset_command))
    
    app.add_handler(CommandHandler(["quizzes"], show_my_quizzes))

    app.add_handler(CallbackQueryHandler(creation_button_handler, pattern="^(finish_creation|cancel_creation)$"))
    app.add_handler(CallbackQueryHandler(button_handler))
    app.add_handler(InlineQueryHandler(inline_query_handler))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, receive_text))
    app.add_handler(PollAnswerHandler(poll_answer_handler))

    if WEBHOOK_URL:
        app.run_webhook(
            listen="0.0.0.0",
            port=PORT,
            url_path=f"telegram/{BOT_TOKEN}",
            secret_token=WEBHOOK_SECRET,
            webhook_url=f"{WEBHOOK_URL}/telegram/{BOT_TOKEN}"
        )
    else:
        logger.info("⚡ Starting Bot in Polling Mode with Background Dummy Server...")
        app.run_polling(drop_pending_updates=True)

if __name__ == "__main__":
    main()
