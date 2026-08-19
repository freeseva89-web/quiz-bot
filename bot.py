
import os
import re
import json
import time
import random
import string
import asyncio
import logging
import html
import uuid
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo
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
# 1. CONFIGURATION
# ==========================================
BOT_TOKEN = os.getenv("BOT_TOKEN", "YOUR_BOT_TOKEN_HERE")
BOT_USERNAME = ""

DATABASE_URL = os.getenv(
    "DATABASE_URL",
    "postgresql://quizuser:password@localhost:5432/quizdb"
)
REDIS_URL = os.getenv("REDIS_URL", "redis://localhost:6379/0")

WEBHOOK_URL = os.getenv("WEBHOOK_URL", "").rstrip("/")
PORT = int(os.getenv("PORT", "10000"))
WEBHOOK_SECRET = os.getenv(
    "WEBHOOK_SECRET",
    "super_secret_webhook_token_123"
)

MAX_TELEGRAM_MSG_LEN = 3800

# ONLY this marker is accepted as the correct-answer marker.
CORRECT_MARK = "✅"

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO
)
logger = logging.getLogger("QuizBot")

db_pool: Optional[asyncpg.Pool] = None
redis_client: Optional[aioredis.Redis] = None
instance_lock_conn = None

telegram_rate_limiter = asyncio.Semaphore(20)
background_tasks: set = set()
schedule_worker_task = None
IST = ZoneInfo("Asia/Kolkata")


# ==========================================
# 2. RENDER HEALTH SERVER
# ==========================================
async def handle_health(request):
    return web.Response(text="Quiz Bot Web Engine Active")


async def start_dummy_server():
    app = web.Application()
    app.router.add_get("/", handle_health)

    runner = web.AppRunner(app)
    await runner.setup()

    site = web.TCPSite(runner, "0.0.0.0", PORT)
    await site.start()

    logger.info("✅ Render Dummy Web Server running on port %s", PORT)


# ==========================================
# 3. GENERAL HELPERS
# ==========================================
def generate_short_code(length: int = 8) -> str:
    chars = string.ascii_uppercase + string.digits
    return "".join(random.choice(chars) for _ in range(length))


def count_correct_marks(text: str) -> int:
    return text.count(CORRECT_MARK)


def remove_correct_marks(text: str) -> str:
    # Only remove the chosen correct-answer marker.
    clean_text = text.replace(CORRECT_MARK, "")
    return re.sub(r"\s+", " ", clean_text).strip()


def get_progress_bar(score: int, total: int) -> str:
    if total <= 0:
        return "▱▱▱▱▱▱▱▱▱▱"

    percentage = (score / total) * 100
    filled = int(round(percentage / 10))
    filled = max(0, min(10, filled))

    return "▰" * filled + "▱" * (10 - filled)


def format_time(seconds: float) -> str:
    total_secs = int(round(seconds))

    if total_secs < 60:
        return f"{total_secs}s"

    mins = total_secs // 60
    secs = total_secs % 60

    return f"{mins}m {secs:02d}s"


def track_task(task: asyncio.Task) -> None:
    background_tasks.add(task)

    def _done_callback(done_task):
        background_tasks.discard(done_task)
        try:
            error = done_task.exception()
        except asyncio.CancelledError:
            return
        if error:
            logger.exception(
                "Background quiz task failed.",
                exc_info=(
                    type(error),
                    error,
                    error.__traceback__
                )
            )

    task.add_done_callback(_done_callback)


def chat_id_display(chat) -> str:
    return str(chat.id)


def safe_html(text: str) -> str:
    return html.escape(str(text), quote=False)


async def check_admin_or_owner(chat, user_id: int, owner_id: str) -> bool:
    if chat.type == "private":
        return True

    if owner_id and str(user_id) == str(owner_id):
        return True

    try:
        chat_member = await chat.get_member(user_id)

        if chat_member.status in ["creator", "administrator"]:
            return True

    except TelegramError as e:
        logger.error("Error checking admin status: %s", e)

    return False


async def is_target_chat_admin_or_owner(chat, user_id: int) -> bool:
    """Check whether the requesting user is an admin/owner of the target chat."""
    if chat.type == "private":
        return True
    try:
        member = await chat.get_member(user_id)
        return member.status in ["creator", "administrator"]
    except TelegramError as e:
        logger.error("Target chat admin check failed: %s", e)
        return False


# ==========================================
# 4. TARGET CHAT / CHANNEL HELPERS
# ==========================================
def normalize_target_input(raw: str) -> Optional[Any]:
    """
    Accept:
      - -1001234567890
      - @username
      - username
      - https://t.me/username
      - https://telegram.me/username
      - https://t.me/c/1234567890/123
      - https://t.me/c/1234567890
    """
    value = raw.strip()

    if not value:
        return None

    # Numeric Chat ID
    if re.fullmatch(r"-?\d+", value):
        try:
            return int(value)
        except ValueError:
            return None

    # Username
    if re.fullmatch(r"@?[A-Za-z0-9_]{5,32}", value):
        return value if value.startswith("@") else f"@{value}"

    # Telegram public/private link
    match = re.match(
        r"^https?://(?:www\.)?(?:t\.me|telegram\.me)/(.+?)/?$",
        value,
        re.IGNORECASE
    )

    if not match:
        return None

    path = match.group(1).split("?", 1)[0].strip("/")

    # Public username link
    if re.fullmatch(r"[A-Za-z0-9_]{5,32}", path):
        return f"@{path}"

    # t.me/c/<internal_id>/<message_id>
    c_match = re.match(r"^c/(\d+)(?:/\d+)?$", path)

    if c_match:
        internal_id = c_match.group(1)

        # Telegram supergroup/channel internal IDs are represented as -100...
        return int(f"-100{internal_id}")

    # Private invite links cannot be resolved by Bot API.
    # User should use Chat ID or public username instead.
    if path.startswith("+") or path.startswith("joinchat/"):
        return None

    return None


async def resolve_target_chat(bot, raw_target: str):
    target = normalize_target_input(raw_target)

    if target is None:
        return None, (
            "❌ Target could not be identified.\n\n"
            "Send one of the following:\n"
            "• @channelusername\n"
            "• Public Channel/Group link\n"
            "• Chat ID such as -1001234567890\n\n"
            "⚠️ The Bot API cannot resolve a private invite link (+...). "
            "Use the Chat ID for such chats."
        )

    try:
        chat = await bot.get_chat(target)
    except TelegramError as e:
        logger.warning("Target get_chat failed for %s: %s", raw_target, e)

        return None, (
            "❌ Target not found or the bot cannot access it.\n\n"
            "Please check:\n"
            "• The link/username is correct\n"
            "• The bot is present in the Channel/Group\n"
            "• The bot has the required admin/send permissions\n"
            "• Use the Chat ID if necessary\n\n"
            f"Telegram: {safe_html(str(e))}"
        )

    if chat.type not in ["channel", "group", "supergroup"]:
        return None, "❌ Only a Channel, Group, or Supergroup can be selected as the target."

    try:
        bot_info = await bot.get_me()
        bot_member = await bot.get_chat_member(chat.id, bot_info.id)
    except TelegramError as e:
        return None, (
            "❌ The bot membership/permissions could not be verified.\n\n"
            f"{safe_html(str(e))}"
        )

    if bot_member.status not in ["creator", "administrator"]:
        return None, (
            "❌ The bot is not an Administrator of this target.\n\n"
            "Make the bot an admin in the Channel/Group and try again."
        )

    # Channels require posting rights.
    if chat.type == "channel":
        can_post = getattr(bot_member, "can_post_messages", None)

        if can_post is False:
            return None, (
                "❌ The bot cannot post in this Channel.\n\n"
                "Make the bot a Channel Admin and "
                "grant the Post Messages permission."
            )

    return chat, None


def target_type_text(chat) -> str:
    if chat.type == "channel":
        return "📢 Channel"
    if chat.type == "supergroup":
        return "👥 Supergroup"
    return "👥 Group"


# ==========================================
# 5. DATABASE & REDIS
# ==========================================
async def init_infrastructure():
    global db_pool, redis_client

    try:
        db_pool = await asyncpg.create_pool(
            dsn=DATABASE_URL,
            min_size=5,
            max_size=25,
            command_timeout=30.0,
            # Disable asyncpg prepared-statement caching because startup migrations
            # ALTER existing tables and PostgreSQL can invalidate cached plans.
            statement_cache_size=0
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

                CREATE INDEX IF NOT EXISTS idx_quizzes_owner_id
                ON quizzes(owner_id);

                CREATE INDEX IF NOT EXISTS idx_quizzes_short_code
                ON quizzes(short_code);

                CREATE TABLE IF NOT EXISTS quiz_results (
                    id SERIAL PRIMARY KEY,
                    quiz_id INT REFERENCES quizzes(id) ON DELETE CASCADE,
                    chat_id BIGINT,
                    user_id BIGINT NOT NULL,
                    user_name TEXT,
                    score INT NOT NULL,
                    total_time DOUBLE PRECISION NOT NULL,
                    completed_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP
                );

                -- Existing installations may have an older quiz_results table
                -- without chat_id. Add it without deleting existing data.
                ALTER TABLE quiz_results
                ADD COLUMN IF NOT EXISTS chat_id BIGINT;

                CREATE INDEX IF NOT EXISTS idx_quiz_results_quiz_chat
                ON quiz_results(quiz_id, chat_id);

                CREATE TABLE IF NOT EXISTS quiz_schedules (
                    id BIGSERIAL PRIMARY KEY,
                    owner_id BIGINT NOT NULL,
                    quiz_id INT,
                    target_chat_id BIGINT NOT NULL,
                    target_username TEXT,
                    quiz_title TEXT NOT NULL,
                    questions JSONB NOT NULL,
                    qshuffle BOOLEAN NOT NULL DEFAULT FALSE,
                    oshuffle BOOLEAN NOT NULL DEFAULT FALSE,
                    explanation BOOLEAN NOT NULL DEFAULT TRUE,
                    timer INT NOT NULL DEFAULT 20,
                    scheduled_at TIMESTAMP WITH TIME ZONE NOT NULL,
                    status VARCHAR(20) NOT NULL DEFAULT 'pending',
                    card_message_id BIGINT,
                    reminder_sent BOOLEAN NOT NULL DEFAULT FALSE,
                    created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP,
                    started_at TIMESTAMP WITH TIME ZONE,
                    completed_at TIMESTAMP WITH TIME ZONE,
                    cancelled_at TIMESTAMP WITH TIME ZONE
                );

                -- Migration-safe schedule columns for installations where
                -- quiz_schedules already existed before the latest schedule version.
                -- CREATE TABLE IF NOT EXISTS does NOT add missing columns to an
                -- existing table, so every schedule column used by the worker is
                -- explicitly checked here.
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS owner_id BIGINT;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS quiz_id INT;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS target_chat_id BIGINT;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS target_username TEXT;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS target_type TEXT DEFAULT 'group';
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS quiz_title TEXT;

                -- Legacy deployments may have a restrictive target_type CHECK
                -- constraint that rejects Telegram supergroups. Telegram returns
                -- normal groups as either 'group' or 'supergroup', so keep all
                -- valid Telegram target types accepted by the scheduler.
                ALTER TABLE quiz_schedules
                    DROP CONSTRAINT IF EXISTS quiz_schedules_target_type_check;

                UPDATE quiz_schedules
                SET target_type = CASE
                    WHEN target_type IN ('group', 'supergroup', 'channel', 'private')
                        THEN target_type
                    ELSE 'group'
                END;

                ALTER TABLE quiz_schedules
                    ADD CONSTRAINT quiz_schedules_target_type_check
                    CHECK (target_type IN ('group', 'supergroup', 'channel', 'private'));

                -- Legacy installations may already have target_type as NOT NULL.
                -- Backfill old rows before any new schedule is inserted.
                UPDATE quiz_schedules
                SET target_type = COALESCE(NULLIF(target_type, ''), 'group')
                WHERE target_type IS NULL OR target_type = '';
                ALTER TABLE quiz_schedules ALTER COLUMN target_type SET DEFAULT 'group';
                ALTER TABLE quiz_schedules ALTER COLUMN target_type SET NOT NULL;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS questions JSONB;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS qshuffle BOOLEAN DEFAULT FALSE;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS oshuffle BOOLEAN DEFAULT FALSE;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS explanation BOOLEAN DEFAULT TRUE;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS timer INT DEFAULT 20;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS scheduled_at TIMESTAMP WITH TIME ZONE;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS status VARCHAR(20) DEFAULT 'pending';
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS card_message_id BIGINT;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS reminder_sent BOOLEAN DEFAULT FALSE;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS created_at TIMESTAMP WITH TIME ZONE DEFAULT CURRENT_TIMESTAMP;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS started_at TIMESTAMP WITH TIME ZONE;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS completed_at TIMESTAMP WITH TIME ZONE;
                ALTER TABLE quiz_schedules ADD COLUMN IF NOT EXISTS cancelled_at TIMESTAMP WITH TIME ZONE;

                -- Backfill safe defaults for rows created by an older version.
                UPDATE quiz_schedules SET qshuffle=FALSE WHERE qshuffle IS NULL;
                UPDATE quiz_schedules SET oshuffle=FALSE WHERE oshuffle IS NULL;
                UPDATE quiz_schedules SET explanation=TRUE WHERE explanation IS NULL;
                UPDATE quiz_schedules SET timer=20 WHERE timer IS NULL;
                UPDATE quiz_schedules SET status='pending' WHERE status IS NULL;
                UPDATE quiz_schedules SET reminder_sent=FALSE WHERE reminder_sent IS NULL;

                CREATE INDEX IF NOT EXISTS idx_quiz_schedules_pending
                ON quiz_schedules(status, scheduled_at);

                CREATE INDEX IF NOT EXISTS idx_quiz_schedules_target_time
                ON quiz_schedules(target_chat_id, scheduled_at);
            """)

        logger.info("✅ PostgreSQL Database Tables & Indexes Verified.")

    except Exception as e:
        logger.critical("❌ PostgreSQL Initialization Failed: %s", e)
        raise

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
        logger.critical("❌ Redis Initialization Failed: %s", e)
        raise


async def save_quiz_async(
    owner_id: int,
    title: str,
    questions: list
) -> Tuple[int, str]:

    if not db_pool:
        raise Exception("Database Pool connection is missing.")

    # Protect against the extremely unlikely short-code collision.
    for _ in range(5):
        short_code = generate_short_code()

        try:
            async with db_pool.acquire() as conn:
                row = await conn.fetchrow(
                    """
                    INSERT INTO quizzes
                    (short_code, owner_id, title, questions)
                    VALUES ($1, $2, $3, $4::jsonb)
                    RETURNING id, short_code
                    """,
                    short_code,
                    owner_id,
                    title,
                    json.dumps(questions, ensure_ascii=False)
                )

                return row["id"], row["short_code"]

        except asyncpg.UniqueViolationError:
            continue

    raise Exception("Could not generate a unique quiz code.")


async def get_my_quizzes_async(owner_id: int):
    if not db_pool:
        return []

    async with db_pool.acquire() as conn:
        return await conn.fetch(
            """
            SELECT id, short_code, title, created_at
            FROM quizzes
            WHERE owner_id=$1
            ORDER BY id DESC
            LIMIT 50
            """,
            owner_id
        )


async def load_quiz_by_code_or_id(identifier: str):
    if not db_pool:
        return None

    async with db_pool.acquire() as conn:
        if identifier.isdigit():
            row = await conn.fetchrow(
                """
                SELECT owner_id, title, questions, short_code, id
                FROM quizzes
                WHERE id=$1 OR short_code=$2
                """,
                int(identifier),
                identifier
            )
        else:
            row = await conn.fetchrow(
                """
                SELECT owner_id, title, questions, short_code, id
                FROM quizzes
                WHERE short_code=$1
                """,
                identifier
            )

        if row:
            questions = (
                json.loads(row["questions"])
                if isinstance(row["questions"], str)
                else row["questions"]
            )

            return (
                row["owner_id"],
                row["title"],
                questions,
                row["short_code"],
                row["id"]
            )

    return None


async def delete_quiz_async(owner_id: int, quiz_id: int) -> bool:
    if not db_pool:
        return False

    async with db_pool.acquire() as conn:
        result = await conn.execute(
            """
            DELETE FROM quizzes
            WHERE id=$1 AND owner_id=$2
            """,
            quiz_id,
            owner_id
        )

    return result != "DELETE 0"


# ==========================================
# 6. QUESTION PARSER
# ==========================================
def parse_questions_flexible(text: str):
    lines = text.splitlines()

    raw_blocks = []
    current_block = []

    question_pattern = re.compile(
        r"^\s*(?:(?:प्रश्न|Question|Q)\s*\d*|\d+)"
        r"\s*[\.\):\-]\s*(.+?)\s*$",
        re.IGNORECASE
    )

    for line in lines:
        stripped = line.strip()

        if not stripped:
            continue

        if question_pattern.match(stripped):
            if current_block:
                raw_blocks.append(current_block)

            current_block = []

        current_block.append(stripped)

    if current_block:
        raw_blocks.append(current_block)

    option_pattern = re.compile(
        r"^\s*([A-Da-d]|[0-9]{1,2})\s*[\.\):\-]\s*(.+?)\s*$"
    )

    valid_questions = []
    skipped_count = 0

    for block in raw_blocks:
        if not block:
            continue

        options = []
        correct_candidates = []
        explanation = ""

        q_match = question_pattern.match(block[0])

        if q_match:
            q_text = q_match.group(1).strip()
        else:
            q_text = block[0].strip()

        for line in block[1:]:
            opt_match = option_pattern.match(line)

            if opt_match:
                raw_opt = opt_match.group(2).strip()

                marks = count_correct_marks(raw_opt)
                opt_clean = remove_correct_marks(raw_opt)

                if opt_clean:
                    options.append(opt_clean)

                    if marks > 0:
                        correct_candidates.append(len(options) - 1)

            else:
                lower = line.lower()

                if (
                    lower.startswith("explanation:")
                    or line.startswith("व्याख्या:")
                ):
                    explanation = line.split(":", 1)[1].strip()

        correct_mark_count = sum(
            count_correct_marks(
                block_line
            )
            for block_line in block[1:]
            if option_pattern.match(block_line)
        )

        if (
            q_text
            and len(q_text) <= 300
            and 2 <= len(options) <= 12
            and correct_mark_count == 1
            and len(correct_candidates) == 1
            and all(1 <= len(o) <= 100 for o in options)
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



# ==========================================
# 6.5. ONE-TIME SCHEDULE SYSTEM
# ==========================================
class ScheduleContext:
    """Small context adapter so scheduled quizzes reuse the existing quiz engine."""
    def __init__(self, bot):
        self.bot = bot
        self.user_data = {}


def format_schedule_ist(dt: datetime) -> str:
    return dt.astimezone(IST).strftime("%d %B %Y, %I:%M %p IST")


def parse_schedule_datetime(text: str) -> Optional[datetime]:
    value = text.strip()
    formats = [
        "%d-%m-%Y %H:%M",
        "%d/%m/%Y %H:%M",
        "%d-%m-%Y %I:%M %p",
        "%d/%m/%Y %I:%M %p",
        "%d %B %Y %H:%M",
        "%d %B %Y %I:%M %p",
    ]
    for fmt in formats:
        try:
            naive = datetime.strptime(value, fmt)
            return naive.replace(tzinfo=IST)
        except ValueError:
            continue
    return None


async def schedule_conflict_exists(target_chat_id: int, scheduled_at: datetime) -> bool:
    if not db_pool:
        return True
    async with db_pool.acquire() as conn:
        row = await conn.fetchrow(
            """
            SELECT id
            FROM quiz_schedules
            WHERE target_chat_id = $1
              AND status = 'pending'
              AND scheduled_at > $2
              AND scheduled_at < $3
            LIMIT 1
            """,
            target_chat_id,
            scheduled_at - timedelta(minutes=5),
            scheduled_at + timedelta(minutes=5)
        )
        return row is not None


async def create_schedule_record(owner_id: int, quiz_id: int, target_chat_id: int,
                                 target_username: str, target_type: str, quiz_title: str,
                                 questions: list, qshuffle: bool, oshuffle: bool,
                                 explanation: bool, timer: int, scheduled_at: datetime) -> int:
    async with db_pool.acquire() as conn:
        row = await conn.fetchrow(
            """
            INSERT INTO quiz_schedules
            (owner_id, quiz_id, target_chat_id, target_username, target_type, quiz_title,
             questions, qshuffle, oshuffle, explanation, timer, scheduled_at)
            VALUES ($1,$2,$3,$4,$5,$6,$7::jsonb,$8,$9,$10,$11,$12)
            RETURNING id
            """,
            owner_id, quiz_id or None, target_chat_id, target_username,
            (target_type if target_type in {"group", "supergroup", "channel", "private"} else "group"),
            quiz_title, json.dumps(questions, ensure_ascii=False),
            qshuffle, oshuffle, explanation, timer, scheduled_at
        )
        return int(row["id"])


async def update_schedule_card(bot, schedule_id: int, text: str, markup=None):
    if not db_pool:
        return
    row = await db_pool.fetchrow(
        "SELECT target_chat_id, card_message_id FROM quiz_schedules WHERE id=$1",
        schedule_id
    )
    if not row or not row["card_message_id"]:
        return
    try:
        await bot.edit_message_text(
            chat_id=int(row["target_chat_id"]),
            message_id=int(row["card_message_id"]),
            text=text,
            parse_mode="HTML",
            reply_markup=markup
        )
    except TelegramError:
        pass


def build_schedule_card(schedule_id: int, title: str, scheduled_at: datetime,
                        timer: int, status: str = "Scheduled") -> tuple[str, InlineKeyboardMarkup]:
    text = (
        f"🧠 <b>{safe_html(title)}</b>\n\n"
        f"📅 Date: <b>{scheduled_at.astimezone(IST).strftime('%d %B %Y')}</b>\n"
        f"🕐 Time: <b>{scheduled_at.astimezone(IST).strftime('%I:%M %p')} IST</b>\n"
        f"🔄 Repeat: <b>No — One Time</b>\n"
        f"⏱ Timer: <b>{timer} Seconds</b>\n"
        f"📌 Status: <b>{safe_html(status)}</b>"
    )
    if status == "Scheduled":
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("❌ Cancel Schedule", callback_data=f"schedule_cancel_{schedule_id}")]
        ])
    else:
        markup = None
    return text, markup


async def send_schedule_card(bot, schedule_id: int):
    row = await db_pool.fetchrow(
        "SELECT * FROM quiz_schedules WHERE id=$1", schedule_id
    )
    if not row:
        return
    text, markup = build_schedule_card(
        schedule_id, row["quiz_title"], row["scheduled_at"], row["timer"]
    )
    msg = await bot.send_message(
        int(row["target_chat_id"]), text,
        parse_mode="HTML", reply_markup=markup
    )
    await db_pool.execute(
        "UPDATE quiz_schedules SET card_message_id=$1 WHERE id=$2",
        msg.message_id, schedule_id
    )


async def show_my_schedules(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.type != "private":
        return
    rows = await db_pool.fetch(
        """
        SELECT id, quiz_title, target_username, target_chat_id, scheduled_at, timer
        FROM quiz_schedules
        WHERE owner_id=$1 AND status='pending'
        ORDER BY scheduled_at ASC
        LIMIT 20
        """, update.effective_user.id
    )
    if not rows:
        await update.message.reply_text("📅 <b>My Schedules</b>\n\nNo pending schedules.", parse_mode="HTML")
        return
    buttons=[]
    lines=["📅 <b>My Schedules</b>", ""]
    for r in rows:
        target = r["target_username"] or str(r["target_chat_id"])
        lines.append(
            f"🧠 <b>{safe_html(r['quiz_title'])}</b>\n"
            f"👥 {safe_html(target)}\n"
            f"🕐 {format_schedule_ist(r['scheduled_at'])}"
        )
        buttons.append([InlineKeyboardButton(f"❌ Cancel: {str(r['quiz_title'])[:24]}", callback_data=f"schedule_cancel_private_{r['id']}")])
    await update.message.reply_text("\n\n".join(lines), parse_mode="HTML", reply_markup=InlineKeyboardMarkup(buttons))


async def schedule_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    if update.effective_chat.type != "private":
        await update.message.reply_text("❌ Please use /schedule in private chat.")
        return
    questions = context.user_data.get("questions", [])
    if not questions:
        await update.message.reply_text(
            "❌ Load a saved quiz first from /quizzes, then press 📅 Schedule."
        )
        return
    context.user_data["schedule_flow"] = {"stage": "target"}
    await update.message.reply_text(
        "📅 <b>Schedule Quiz</b>\n\n"
        f"🧠 Quiz: <b>{safe_html(context.user_data.get('quiz_title','Quiz'))}</b>\n\n"
        "Send the target group <b>username or public link</b>.\n"
        "Example: <code>@myquizgroup</code> or <code>https://t.me/myquizgroup</code>\n\n"
        "Only a Group/Supergroup is allowed. The bot must be an Admin there.",
        parse_mode="HTML"
    )


async def process_schedule_text(update: Update, context: ContextTypes.DEFAULT_TYPE, text: str) -> bool:
    flow = context.user_data.get("schedule_flow")
    if not flow:
        return False
    if flow.get("stage") == "target":
        chat, error = await resolve_target_chat(context.bot, text)
        if error:
            await update.message.reply_text(error)
            return True
        if chat.type not in ["group", "supergroup"]:
            await update.message.reply_text("❌ Schedule target must be a Group or Supergroup.")
            return True
        if not await is_target_chat_admin_or_owner(chat, update.effective_user.id):
            await update.message.reply_text("❌ Only that Group's Admin or Owner can schedule a quiz there.")
            return True
        flow["target_chat_id"] = chat.id
        flow["target_username"] = chat.username and f"@{chat.username}" or str(chat.id)
        flow["stage"] = "datetime"
        await update.message.reply_text(
            f"✅ Target verified: <b>{safe_html(flow['target_username'])}</b>\n\n"
            "Now send India time in this format:\n"
            "<code>25-08-2026 20:00</code>\n\n"
            "🇮🇳 Time zone: <b>Asia/Kolkata (IST)</b>\n"
            "No repeat — this schedule runs once.",
            parse_mode="HTML"
        )
        return True
    if flow.get("stage") == "datetime":
        dt = parse_schedule_datetime(text)
        if not dt:
            await update.message.reply_text("❌ Invalid date/time. Use <code>25-08-2026 20:00</code>.", parse_mode="HTML")
            return True
        now = datetime.now(IST)
        if dt <= now:
            await update.message.reply_text("❌ Schedule time must be in the future.")
            return True
        if dt - now < timedelta(minutes=1):
            await update.message.reply_text("❌ Schedule at least 1 minute in the future so it can be confirmed safely.")
            return True
        if await schedule_conflict_exists(flow["target_chat_id"], dt):
            await update.message.reply_text(
                "❌ This group already has another schedule within 5 minutes of that time.\n\n"
                "Please choose a time with at least a 5-minute gap."
            )
            return True
        # Re-verify permissions at final confirmation time.
        chat, error = await resolve_target_chat(context.bot, flow["target_username"])
        if error or not chat or not await is_target_chat_admin_or_owner(chat, update.effective_user.id):
            await update.message.reply_text("❌ Final verification failed. You must still be an Admin/Owner and the bot must still be an Admin in that group.")
            context.user_data.pop("schedule_flow", None)
            return True
        q = deepcopy(context.user_data.get("questions", []))
        title = context.user_data.get("quiz_title", "Quiz")
        qshuffle = bool(context.user_data.get("qshuffle", False))
        oshuffle = bool(context.user_data.get("oshuffle", False))
        explanation = bool(context.user_data.get("explanation", True))
        timer = int(context.user_data.get("timer", 20))
        # chat.type is guaranteed by Telegram after final verification; keep a
        # defensive fallback so legacy/edge cases can never insert NULL.
        verified_target_type = chat.type or "group"
        try:
            schedule_id = await create_schedule_record(
                update.effective_user.id,
                int(context.user_data.get("quiz_id", 0) or 0),
                chat.id,
                flow["target_username"], verified_target_type, title, q, qshuffle, oshuffle, explanation, timer, dt
            )
        except Exception:
            logger.exception(
                "❌ Schedule database insert failed: chat_id=%s target_type=%s scheduled_at=%s",
                chat.id, verified_target_type, dt.isoformat()
            )
            await update.message.reply_text(
                "❌ Schedule could not be saved because the database rejected the schedule. "
                "The schedule was NOT marked as scheduled. Please try again after the bot restarts."
            )
            return True

        logger.info(
            "📅 Schedule created: id=%s chat_id=%s target_type=%s scheduled_at=%s owner_id=%s",
            schedule_id, chat.id, verified_target_type, dt.isoformat(), update.effective_user.id
        )
        try:
            await send_schedule_card(context.bot, schedule_id)
        except TelegramError:
            # The DB schedule is already valid; card delivery failure must not
            # destroy the actual schedule. The worker will still execute it.
            logger.exception("Could not send schedule card id=%s", schedule_id)

        await update.message.reply_text(
            "✅ <b>Quiz Scheduled Successfully</b>\n\n"
            f"📌 Quiz: <b>{safe_html(title)}</b>\n"
            f"👥 Group: <b>{safe_html(flow['target_username'])}</b>\n"
            f"📅 Date: <b>{dt.strftime('%d %B %Y')}</b>\n"
            f"🕐 Time: <b>{dt.strftime('%I:%M %p')} IST</b>\n"
            "🔄 Repeat: <b>No — One Time</b>\n"
            f"⏱ Timer: <b>{timer} Seconds</b>\n\n"
            "The quiz will automatically start in the selected group at the scheduled time.",
            parse_mode="HTML"
        )
        context.user_data.pop("schedule_flow", None)
        return True
    return False


async def cancel_schedule(schedule_id: int, user_id: int, target_chat=None) -> tuple[bool, str]:
    row = await db_pool.fetchrow("SELECT * FROM quiz_schedules WHERE id=$1", schedule_id)
    if not row:
        return False, "Schedule not found."
    if row["status"] != "pending":
        return False, "This schedule is no longer pending."
    allowed = int(row["owner_id"]) == int(user_id)
    if target_chat is not None:
        allowed = allowed or await is_target_chat_admin_or_owner(target_chat, user_id)
    if not allowed:
        return False, "Only the Group Admin/Owner can cancel this schedule."
    updated = await db_pool.execute(
        "UPDATE quiz_schedules SET status='cancelled', cancelled_at=CURRENT_TIMESTAMP WHERE id=$1 AND status='pending'",
        schedule_id
    )
    if updated.endswith("1"):
        return True, "Schedule cancelled."
    return False, "Schedule could not be cancelled."


async def schedule_worker(application: Application):
    logger.info("📅 Schedule worker started (IST, one-time schedules).")
    while True:
        try:
            now = datetime.now(timezone.utc)
            # Five-minute reminder, once per schedule.
            reminder_rows = await db_pool.fetch(
                """
                SELECT * FROM quiz_schedules
                WHERE status='pending'
                  AND reminder_sent=FALSE
                  AND scheduled_at > $1
                  AND scheduled_at <= $2
                """, now, now + timedelta(minutes=5)
            )
            for row in reminder_rows:
                try:
                    await application.bot.send_message(
                        int(row["target_chat_id"]),
                        "🔔 Scheduled quiz is starting in 5 minutes!"
                    )
                    updated = await db_pool.execute(
                        "UPDATE quiz_schedules SET reminder_sent=TRUE WHERE id=$1 AND status='pending' AND reminder_sent=FALSE",
                        row["id"]
                    )
                    logger.info("🔔 Schedule reminder sent: id=%s result=%s", row["id"], updated)
                except TelegramError:
                    logger.exception("Failed to send schedule reminder id=%s", row["id"])

            due_rows = await db_pool.fetch(
                """
                SELECT * FROM quiz_schedules
                WHERE status='pending' AND scheduled_at <= $1
                ORDER BY scheduled_at ASC
                LIMIT 20
                """, now
            )
            for row in due_rows:
                # Atomic claim so a future multi-instance deployment cannot run it twice.
                claimed = await db_pool.fetchrow(
                    """
                    UPDATE quiz_schedules
                    SET status='running', started_at=CURRENT_TIMESTAMP
                    WHERE id=$1 AND status='pending'
                    RETURNING *
                    """, row["id"]
                )
                if not claimed:
                    continue
                # Run independently so reminders for other groups continue while
                # this quiz is running. Per-group Redis locking preserves queue order.
                task = asyncio.create_task(run_one_schedule(application, claimed))
                track_task(task)

            await asyncio.sleep(5)
        except asyncio.CancelledError:
            logger.info("📅 Schedule worker stopped.")
            raise
        except Exception:
            logger.exception("Schedule worker error; retrying.")
            await asyncio.sleep(5)


async def run_one_schedule(application: Application, row):
    schedule_id = int(row["id"])
    chat_id = int(row["target_chat_id"])
    lock = redis_client.lock(f"lock:schedule_start:{chat_id}", timeout=30)
    try:
        # Only one scheduled quiz may pass the start gate for a group at a time.
        # Other schedules wait here until the current quiz finishes.
        while True:
            acquired = await lock.acquire(blocking=False)
            if not acquired:
                await asyncio.sleep(2)
                continue
            try:
                if await redis_client.get(f"quiz_active:{chat_id}"):
                    # Release while waiting so the currently running quiz and other
                    # scheduler operations are never blocked by this task.
                    pass
                else:
                    break
            finally:
                if await redis_client.get(f"quiz_active:{chat_id}"):
                    try:
                        await lock.release()
                    except Exception:
                        pass
            await asyncio.sleep(2)

        # Final 5-minute rule check against any still-pending schedule.
        adapter = ScheduleContext(application.bot)
        adapter.user_data.update({
            "owner_id": int(row["owner_id"]),
            "quiz_id": int(row["quiz_id"] or 0),
            "quiz_title": row["quiz_title"],
            "questions": json.loads(row["questions"]) if isinstance(row["questions"], str) else row["questions"],
            "qshuffle": bool(row["qshuffle"]),
            "oshuffle": bool(row["oshuffle"]),
            "explanation": bool(row["explanation"]),
            "timer": int(row["timer"]),
        })
        await begin_quiz(chat_id, adapter, schedule_id=schedule_id)
        try:
            await lock.release()
        except Exception:
            pass

        # begin_quiz can refuse because a quiz became active between checks.
        # If so, leave the schedule as completed only after the scheduled quiz's
        # own active state has actually appeared; otherwise retry as pending.
        await asyncio.sleep(1)
        live_state = await redis_client.hgetall(f"quiz_state:{chat_id}")
        if (not await redis_client.get(f"quiz_active:{chat_id}")
                or str(live_state.get("schedule_id", "")) != str(schedule_id)):
            await db_pool.execute("UPDATE quiz_schedules SET status='pending', started_at=NULL WHERE id=$1 AND status='running'", schedule_id)
            return

        while await redis_client.get(f"quiz_active:{chat_id}"):
            await asyncio.sleep(3)

        await db_pool.execute(
            "UPDATE quiz_schedules SET status='completed', completed_at=CURRENT_TIMESTAMP WHERE id=$1",
            schedule_id
        )
        await update_schedule_card(
            application.bot, schedule_id,
            *build_schedule_card(schedule_id, row["quiz_title"], row["scheduled_at"], row["timer"], "Completed")
        )
    except Exception:
        logger.exception("Scheduled quiz failed id=%s", schedule_id)
        try:
            await lock.release()
        except Exception:
            pass
        await db_pool.execute(
            "UPDATE quiz_schedules SET status='pending', started_at=NULL WHERE id=$1 AND status='running'",
            schedule_id
        )


async def recover_running_schedules(application: Application):
    """Recover schedules across Render restarts without duplicating a quiz already running."""
    rows = await db_pool.fetch(
        "SELECT * FROM quiz_schedules WHERE status='running'"
    )
    for row in rows:
        chat_id = int(row["target_chat_id"])
        state = await redis_client.hgetall(f"quiz_state:{chat_id}")
        if (await redis_client.get(f"quiz_active:{chat_id}")
                and str(state.get("schedule_id", "")) == str(row["id"])):
            task = asyncio.create_task(wait_for_existing_schedule(application, row))
            track_task(task)
        else:
            await db_pool.execute(
                "UPDATE quiz_schedules SET status='pending', started_at=NULL WHERE id=$1 AND status='running'",
                row["id"]
            )


async def wait_for_existing_schedule(application: Application, row):
    schedule_id = int(row["id"])
    chat_id = int(row["target_chat_id"])
    try:
        while await redis_client.get(f"quiz_active:{chat_id}"):
            await asyncio.sleep(3)
        await db_pool.execute(
            "UPDATE quiz_schedules SET status='completed', completed_at=CURRENT_TIMESTAMP WHERE id=$1 AND status='running'",
            schedule_id
        )
        await update_schedule_card(
            application.bot, schedule_id,
            *build_schedule_card(schedule_id, row["quiz_title"], row["scheduled_at"], row["timer"], "Completed")
        )
    except Exception:
        logger.exception("Failed recovering running schedule id=%s", schedule_id)
        await db_pool.execute(
            "UPDATE quiz_schedules SET status='pending', started_at=NULL WHERE id=$1 AND status='running'",
            schedule_id
        )


# ==========================================
# 7. UI
# ==========================================
def build_settings_keyboard(data: dict) -> InlineKeyboardMarkup:
    q_shuffle = "ON" if data.get("qshuffle") else "OFF"
    o_shuffle = "ON" if data.get("oshuffle") else "OFF"
    explanation = "ON" if data.get("explanation") else "OFF"

    timer = data.get("timer", 20)
    short_code = data.get("short_code", "")

    keyboard = [
        [
            InlineKeyboardButton(
                "▶️ Start Quiz",
                callback_data="start_quiz"
            )
        ]
    ]

    if short_code:
        group_url = (
            f"https://t.me/{BOT_USERNAME}"
            f"?startgroup=quiz_{short_code}"
        )

        keyboard.append([
            InlineKeyboardButton(
                "➕ Start in Group",
                url=group_url
            )
        ])

        keyboard.append([
            InlineKeyboardButton(
                "📲 Share Quiz",
                switch_inline_query=f"quiz:{short_code}"
            )
        ])

        keyboard.append([
            InlineKeyboardButton(
                "📤 Share Polls",
                callback_data="publish_polls"
            )
        ])

        keyboard.append([
            InlineKeyboardButton(
                "📅 Schedule",
                callback_data="schedule_quiz"
            )
        ])

    keyboard.extend([
        [
            InlineKeyboardButton(
                f"🔀 Qs: {q_shuffle}",
                callback_data="toggle_qshuffle"
            ),
            InlineKeyboardButton(
                f"🔀 Opts: {o_shuffle}",
                callback_data="toggle_oshuffle"
            )
        ],
        [
            InlineKeyboardButton(
                f"💡 Exp: {explanation}",
                callback_data="toggle_exp"
            )
        ],
        [
            InlineKeyboardButton(
                f"{'🔘 ' if timer == 10 else ''}10s",
                callback_data="set_timer_10"
            ),
            InlineKeyboardButton(
                f"{'🔘 ' if timer == 15 else ''}15s",
                callback_data="set_timer_15"
            ),
            InlineKeyboardButton(
                f"{'🔘 ' if timer == 20 else ''}20s",
                callback_data="set_timer_20"
            )
        ],
        [
            InlineKeyboardButton(
                f"{'🔘 ' if timer == 30 else ''}30s",
                callback_data="set_timer_30"
            ),
            InlineKeyboardButton(
                f"{'🔘 ' if timer == 45 else ''}45s",
                callback_data="set_timer_45"
            ),
            InlineKeyboardButton(
                f"{'🔘 ' if timer == 60 else ''}60s",
                callback_data="set_timer_60"
            )
        ]
    ])

    return InlineKeyboardMarkup(keyboard)


def build_start_keyboard():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "📝 Create Quiz",
                callback_data="create"
            )
        ],
        [
            InlineKeyboardButton(
                "📚 My Quizzes",
                callback_data="my_quizzes"
            )
        ],
        [
            InlineKeyboardButton(
                "❓ Help",
                callback_data="help"
            )
        ]
    ])


def build_creation_done_keyboard():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "✅ Done Adding Questions",
                callback_data="finish_creation"
            )
        ],
        [
            InlineKeyboardButton(
                "❌ Cancel",
                callback_data="cancel_creation"
            )
        ]
    ])


def build_publish_target_keyboard():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "❌ Cancel",
                callback_data="cancel_publish"
            )
        ]
    ])


# ==========================================
# 8. START / HELP / INLINE
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
                "qshuffle": context.user_data.get(
                    "qshuffle", False
                ),
                "oshuffle": context.user_data.get(
                    "oshuffle", False
                ),
                "explanation": context.user_data.get(
                    "explanation", True
                ),
                "timer": context.user_data.get(
                    "timer", 20
                )
            })

            if update.effective_chat.type in [
                "group",
                "supergroup"
            ]:
                if not await is_target_chat_admin_or_owner(
                    update.effective_chat,
                    update.effective_user.id
                ):
                    await update.message.reply_text(
                        "❌ Only the Group Admin or Owner can start a quiz in this group."
                    )
                    return

                await begin_quiz(
                    update.effective_chat.id,
                    context
                )
                return

            share_link = (
                f"@{BOT_USERNAME} quiz:{short_code}"
            )

            await update.message.reply_text(
                f"👍 Loaded: <b>{safe_html(title)}</b>\n"
                f"📋 Questions: {len(questions)}\n\n"
                f"Share Code:\n"
                f"<code>{safe_html(share_link)}</code>",
                parse_mode="HTML",
                reply_markup=build_settings_keyboard(
                    context.user_data
                )
            )

            return

    await update.message.reply_text(
        "🤖 <b>ENTERPRISE HIGH-SCALE QUIZ BOT</b>\n\n"
        "Select an option below:",
        parse_mode="HTML",
        reply_markup=build_start_keyboard()
    )


async def help_handler(update: Update, context: ContextTypes.DEFAULT_TYPE):
    help_text = (
        "📖 <b>Quiz Bot Help</b>\n\n"
        "• /start - Start the bot\n"
        "• /create - Create a new quiz\n"
        "• /quizzes - My saved quizzes\n"
        "• /schedule - Schedule the currently loaded quiz in a group\n"
        "• /schedules - View your pending schedules\n"
        "• /done - Finish question adding\n"
        "• /postchannel - Send saved questions as native polls\n"
        "• /stop or /pause - Pause active quiz\n"
        "• /cancel - Cancel active quiz\n"
        "• /resetquiz - Reset active quiz state\n"
        "• /help - Show this help\n\n"
        "<b>Correct answer:</b>\n"
        "Only <code>✅</code> is used.\n\n"
        "Example:\n"
        "<code>A. Delhi\n"
        "B. Mumbai\n"
        "C. ✅ Lucknow\n"
        "D. Patna</code>\n\n"
        "📤 <b>Share Polls</b> lets you send all saved "
        "questions as native Telegram Quiz Polls to a "
        "Channel, Group or Supergroup."
    )

    if update.message:
        await update.message.reply_text(
            help_text,
            parse_mode="HTML"
        )


async def inline_query_handler(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    query = update.inline_query.query.strip()

    if not query:
        return

    code = (
        query
        .replace("quiz_", "")
        .replace("quiz:", "")
        .strip()
    )

    loaded = await load_quiz_by_code_or_id(code)

    results = []

    if loaded:
        _, title, questions, short_code, _ = loaded

        start_link = (
            f"https://t.me/{BOT_USERNAME}"
            f"?start=quiz_{short_code}"
        )

        start_group_link = (
            f"https://t.me/{BOT_USERNAME}"
            f"?startgroup=quiz_{short_code}"
        )

        message_text = (
            f"🎲 Quiz • <b>{safe_html(title)}</b>\n\n"
            f"🖊 <b>{len(questions)} questions</b>"
        )

        keyboard = InlineKeyboardMarkup([
            [
                InlineKeyboardButton(
                    "▶️ Start this quiz",
                    url=start_link
                )
            ],
            [
                InlineKeyboardButton(
                    "👥 Start quiz in group",
                    url=start_group_link
                )
            ],
            [
                InlineKeyboardButton(
                    "🔗 Share quiz",
                    switch_inline_query=f"quiz:{short_code}"
                )
            ]
        ])

        results.append(
            InlineQueryResultArticle(
                id=short_code,
                title=f"■ {title} ■",
                description=f"{len(questions)} questions",
                input_message_content=InputTextMessageContent(
                    message_text,
                    parse_mode="HTML"
                ),
                reply_markup=keyboard
            )
        )

    await update.inline_query.answer(
        results,
        cache_time=1,
        is_personal=True
    )


# ==========================================
# 9. CREATE QUIZ
# ==========================================
async def create_command(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    if update.effective_chat.type != "private":
        return

    context.user_data.clear()

    context.user_data["owner_id"] = update.effective_user.id
    context.user_data["waiting_title"] = True
    context.user_data["temp_questions"] = []

    await update.message.reply_text(
        "📝 <b>Send Your Quiz Title</b>",
        parse_mode="HTML"
    )


async def save_current_quiz(
    user_id: int,
    context: ContextTypes.DEFAULT_TYPE
):
    questions = context.user_data.get("temp_questions", [])

    title = context.user_data.get(
        "quiz_title",
        "Untitled Quiz"
    )

    if not questions:
        return None

    quiz_id, short_code = await save_quiz_async(
        user_id,
        title,
        questions
    )

    context.user_data["waiting_title"] = False
    context.user_data["waiting_questions"] = False
    context.user_data["temp_questions"] = []

    context.user_data.update({
        "quiz_id": quiz_id,
        "short_code": short_code,
        "questions": questions,
        "qshuffle": False,
        "oshuffle": False,
        "explanation": True,
        "timer": 20,
        "publish_target": None,
        "publish_target_raw": None
    })

    return quiz_id, short_code, title, questions


async def done_command(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    # This command is only for private chat.
    if update.effective_chat.type != "private":
        return

    questions = context.user_data.get("temp_questions", [])

    if not questions:
        await update.message.reply_text(
            "❌ No questions added."
        )
        return

    user_id = update.effective_user.id

    try:
        saved = await save_current_quiz(
            user_id,
            context
        )

    except Exception:
        logger.exception("Quiz save failed.")

        await update.message.reply_text(
            "❌ Failed to save quiz. Please try again later."
        )

        return

    _, short_code, title, questions = saved

    share_link = (
        f"@{BOT_USERNAME} quiz:{short_code}"
    )

    await update.message.reply_text(
        f"✅ <b>Quiz Created Successfully!</b>\n\n"
        f"📌 Title: <b>{safe_html(title)}</b>\n"
        f"📋 Questions: {len(questions)}\n\n"
        f"Share Code:\n"
        f"<code>{safe_html(share_link)}</code>",
        parse_mode="HTML",
        reply_markup=build_settings_keyboard(
            context.user_data
        )
    )


# ==========================================
# 10. STOP / CANCEL / RESET
# ==========================================
async def stop_command(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    chat = update.effective_chat
    user = update.effective_user
    chat_key = str(chat.id)

    is_active = await redis_client.get(
        f"quiz_active:{chat_key}"
    )

    if not is_active:
        await update.message.reply_text(
            "❌ No active quiz running in this chat."
        )
        return

    owner_id = await redis_client.hget(
        f"quiz_state:{chat_key}",
        "owner_id"
    )

    is_authorized = await check_admin_or_owner(
        chat,
        user.id,
        owner_id
    )

    if not is_authorized:
        await update.message.reply_text(
            "⚠️ Permission Denied! Only Group Admins "
            "or Quiz Host can pause the quiz."
        )
        return

    await redis_client.set(
        f"quiz_pause:{chat_key}",
        "1",
        ex=86400
    )

    current_poll = await redis_client.hgetall(
        f"quiz_current_poll:{chat_key}"
    )
    if current_poll.get("message_id"):
        try:
            await context.bot.stop_poll(
                chat.id,
                int(current_poll["message_id"])
            )
        except TelegramError:
            pass

    keyboard = InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "▶️ Resume Quiz",
                callback_data=f"resume_quiz_{chat_key}"
            )
        ]
    ])

    await update.message.reply_text(
        "⏸️ <b>Quiz Paused.</b>\n"
        "Click the button below to resume:",
        parse_mode="HTML",
        reply_markup=keyboard
    )


async def cancel_command(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    chat = update.effective_chat
    user = update.effective_user
    chat_key = str(chat.id)

    is_active = await redis_client.get(
        f"quiz_active:{chat_key}"
    )

    if not is_active:
        await update.message.reply_text(
            "❌ No active quiz running in this chat."
        )
        return

    owner_id = await redis_client.hget(
        f"quiz_state:{chat_key}",
        "owner_id"
    )

    is_authorized = await check_admin_or_owner(
        chat,
        user.id,
        owner_id
    )

    if not is_authorized:
        await update.message.reply_text(
            "⚠️ Permission Denied! Only Group Admins "
            "or Quiz Host can cancel the quiz."
        )
        return

    await redis_client.set(
        f"quiz_stop:{chat_key}",
        "1",
        ex=3600
    )

    await redis_client.set(
        f"quiz_cancelled:{chat_key}",
        "1",
        ex=3600
    )

    await redis_client.delete(
        f"quiz_pause:{chat_key}"
    )

    current_poll = await redis_client.hgetall(
        f"quiz_current_poll:{chat_key}"
    )
    if current_poll.get("message_id"):
        try:
            await context.bot.stop_poll(
                chat.id,
                int(current_poll["message_id"])
            )
        except TelegramError:
            pass

    await update.message.reply_text(
        "🛑 Quiz completely cancelled. No result will be generated."
    )


async def force_reset_command(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    chat = update.effective_chat
    user = update.effective_user
    chat_key = str(chat.id)

    owner_id = await redis_client.hget(
        f"quiz_state:{chat_key}",
        "owner_id"
    )

    is_authorized = await check_admin_or_owner(
        chat,
        user.id,
        owner_id
    )

    if not is_authorized:
        await update.message.reply_text(
            "⚠️ Permission Denied! Only Group Admins "
            "or Quiz Host can reset the quiz."
        )
        return

    await redis_client.set(
        f"quiz_reset:{chat_key}",
        "1",
        ex=60
    )
    await redis_client.set(
        f"quiz_stop:{chat_key}",
        "1",
        ex=60
    )

    current_poll = await redis_client.hgetall(
        f"quiz_current_poll:{chat_key}"
    )
    if current_poll.get("message_id"):
        try:
            await context.bot.stop_poll(
                chat.id,
                int(current_poll["message_id"])
            )
        except TelegramError:
            pass

    await redis_client.delete(
        f"quiz_active:{chat_key}",
        f"quiz_state:{chat_key}",
        f"quiz_pause:{chat_key}",
        f"quiz_next:{chat_key}",
        f"quiz_index:{chat_key}",
        f"quiz_current_poll:{chat_key}",
        f"quiz_cancelled:{chat_key}",
        f"participants:{chat_key}",
        f"scores:{chat_key}",
        f"times:{chat_key}",
        f"leaderboard:{chat_key}"
    )

    context.user_data.pop("active_quiz_questions", None)
    context.user_data.pop("active_oshuffle", None)
    context.user_data.pop("active_explanation", None)

    await update.message.reply_text(
        "🧹 <b>Quiz state completely reset!</b>\n"
        "You can start a new quiz now.",
        parse_mode="HTML"
    )


async def resume_quiz_callback(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    query = update.callback_query
    chat = query.message.chat
    user = query.from_user
    chat_key = str(chat.id)

    if not await redis_client.get(f"quiz_pause:{chat_key}"):
        await query.answer(
            "❌ No paused quiz found.",
            show_alert=True
        )
        return

    owner_id = await redis_client.hget(
        f"quiz_state:{chat_key}",
        "owner_id"
    )

    if not await check_admin_or_owner(chat, user.id, owner_id):
        await query.answer(
            "⚠️ Sirf Admin ya Quiz Host hi quiz resume kar sakta hai!",
            show_alert=True
        )
        return

    # Prevent two admins from starting two resume loops at once.
    lock = redis_client.lock(
        f"lock:quiz_resume:{chat_key}",
        timeout=10
    )
    acquired = await lock.acquire(blocking=False)
    if not acquired:
        await query.answer(
            "⏳ Quiz resume already in progress.",
            show_alert=True
        )
        return

    try:
        # Re-check after acquiring the lock.
        if not await redis_client.get(f"quiz_pause:{chat_key}"):
            await query.answer(
                "❌ Quiz is already resumed.",
                show_alert=True
            )
            return

        state = await redis_client.hgetall(
            f"quiz_state:{chat_key}"
        )

        raw_questions = state.get("questions")
        if not raw_questions:
            await query.answer(
                "❌ Saved quiz state is missing. Start the quiz again.",
                show_alert=True
            )
            return

        try:
            questions = json.loads(raw_questions)
            start_index = max(
                1,
                int(
                    await redis_client.get(
                        f"quiz_index:{chat_key}"
                    ) or 1
                )
            )
            timer = int(state.get("timer", 20))
        except (TypeError, ValueError, json.JSONDecodeError):
            await query.answer(
                "❌ Saved quiz state is corrupted. Start the quiz again.",
                show_alert=True
            )
            return

        if not isinstance(questions, list) or not questions:
            await query.answer(
                "❌ Saved quiz questions are invalid. Start the quiz again.",
                show_alert=True
            )
            return

        oshuffle = state.get("oshuffle", "0") == "1"
        explanation_enable = state.get("explanation", "1") == "1"

        # Resume from the current question; the stopped Telegram poll is already closed.
        await redis_client.delete(f"quiz_pause:{chat_key}")
        await query.answer("▶️ Quiz resumed.")

        try:
            await query.edit_message_text(
                "▶️ <b>Quiz resumed.</b> Current question se continue hoga...",
                parse_mode="HTML"
            )
        except TelegramError:
            pass

        await asyncio.sleep(0.2)

        task = asyncio.create_task(
            run_quiz_loop(
                chat_key=chat_key,
                chat_id=chat.id,
                questions=questions,
                context=context,
                oshuffle=oshuffle,
                explanation_enable=explanation_enable,
                timer=timer,
                start_index=start_index,
                session_id=state.get("session_id")
            )
        )
        track_task(task)
    finally:
        try:
            await lock.release()
        except Exception:
            pass


# ==========================================
# 11. MY QUIZZES
# ==========================================
async def show_my_quizzes(
    query_or_update,
    context: ContextTypes.DEFAULT_TYPE
):
    if hasattr(query_or_update, "from_user"):
        user_id = query_or_update.from_user.id
    else:
        user_id = query_or_update.effective_user.id

    quizzes = await get_my_quizzes_async(user_id)

    if not quizzes:
        msg = "📚 No saved quizzes found."

        if hasattr(query_or_update, "edit_message_text"):
            await query_or_update.edit_message_text(
                msg,
                parse_mode="HTML"
            )
        else:
            await query_or_update.message.reply_text(
                msg,
                parse_mode="HTML"
            )

        return

    buttons = []

    for row in quizzes[:15]:
        title = str(row["title"])

        if len(title) > 28:
            title = title[:25] + "..."

        buttons.append([
            InlineKeyboardButton(
                f"▶️ {title}",
                callback_data=f"load_{row['short_code']}"
            ),
            InlineKeyboardButton(
                "🗑 Delete",
                callback_data=f"del_{row['id']}"
            )
        ])

    buttons.append([
        InlineKeyboardButton(
            "⬅️ Back",
            callback_data="back_start"
        )
    ])

    markup = InlineKeyboardMarkup(buttons)

    if hasattr(query_or_update, "edit_message_text"):
        await query_or_update.edit_message_text(
            "📚 <b>MY QUIZZES</b>",
            parse_mode="HTML",
            reply_markup=markup
        )
    else:
        await query_or_update.message.reply_text(
            "📚 <b>MY QUIZZES</b>",
            parse_mode="HTML",
            reply_markup=markup
        )


# ==========================================
# 12. PUBLISH POLLS
# ==========================================
async def start_publish_polls(
    query,
    context: ContextTypes.DEFAULT_TYPE
):
    questions = context.user_data.get("questions", [])

    if not questions:
        await query.answer(
            "❌ No questions loaded.",
            show_alert=True
        )
        return

    if len(questions) > 1000:
        await query.answer(
            "❌ Maximum 1000 questions per publish batch.",
            show_alert=True
        )
        return

    context.user_data["waiting_publish_target"] = True
    context.user_data["publish_target"] = None
    context.user_data["publish_target_raw"] = None

    await query.answer()

    await query.message.reply_text(
        "📤 <b>Share Polls</b>\n\n"
        "Send one of the following Channel/Group identifiers:\n\n"
        "🔗 Public Link:\n"
        "<code>https://t.me/example</code>\n\n"
        "👤 Username:\n"
        "<code>@example</code>\n\n"
        "🆔 Chat ID:\n"
        "<code>-1001234567890</code>\n\n"
        "⚠️ Use the Chat ID instead of a private invite link (+...).\n\n"
        f"📋 Total Polls: <b>{len(questions)}</b>",
        parse_mode="HTML",
        reply_markup=build_publish_target_keyboard()
    )


async def verify_and_prepare_publish(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE,
    raw_target: str
):
    if not context.user_data.get("questions"):
        context.user_data["waiting_publish_target"] = False

        await update.message.reply_text(
            "❌ No questions are loaded."
        )
        return

    await update.message.reply_text(
        "🔍 Verifying target..."
    )

    chat, error_message = await resolve_target_chat(
        context.bot,
        raw_target
    )

    if error_message:
        await update.message.reply_text(
            error_message,
            parse_mode="HTML"
        )
        return

    if not await is_target_chat_admin_or_owner(
        chat,
        update.effective_user.id
    ):
        target_name = "Channel" if chat.type == "channel" else "Group"
        await update.message.reply_text(
            f"❌ Only the {target_name} Admin or Owner can send polls to this {target_name}."
        )
        return

    context.user_data["waiting_publish_target"] = False
    context.user_data["publish_target"] = chat.id
    context.user_data["publish_target_raw"] = raw_target

    questions = context.user_data.get("questions", [])

    display_name = chat.title or (
        f"@{chat.username}"
        if chat.username
        else str(chat.id)
    )

    keyboard = InlineKeyboardMarkup([
        [
            InlineKeyboardButton(
                "🚀 SEND ALL POLLS",
                callback_data="confirm_publish_polls"
            )
        ],
        [
            InlineKeyboardButton(
                "🔄 Change Target",
                callback_data="change_publish_target"
            )
        ],
        [
            InlineKeyboardButton(
                "❌ Cancel",
                callback_data="cancel_publish"
            )
        ]
    ])

    await update.message.reply_text(
        "✅ <b>Target Verified</b>\n\n"
        f"{target_type_text(chat)}: "
        f"<b>{safe_html(display_name)}</b>\n"
        f"🆔 Chat ID: <code>{chat.id}</code>\n\n"
        f"📋 Polls to send: <b>{len(questions)}</b>\n\n"
        "Each question will be sent as a separate <b>native Telegram Quiz Poll</b> "
        "as a native Telegram Quiz Poll.\n\n"
        "A Quiz Title is not required.\n"
        "The correct option <b>✅</b> will be set automatically from <b>✅</b>.",
        parse_mode="HTML",
        reply_markup=keyboard
    )


async def publish_all_polls(
    query,
    context: ContextTypes.DEFAULT_TYPE
):
    target_chat_id = context.user_data.get("publish_target")
    questions = deepcopy(
        context.user_data.get("questions", [])
    )

    if not target_chat_id:
        await query.answer(
            "❌ Target missing.",
            show_alert=True
        )
        return

    if not questions:
        await query.answer(
            "❌ No questions found.",
            show_alert=True
        )
        return

    # Prevent two simultaneous publish jobs from the same user.
    if context.user_data.get("publishing_polls"):
        await query.answer(
            "⏳ Polls already being sent.",
            show_alert=True
        )
        return

    context.user_data["publishing_polls"] = True

    await query.answer(
        "🚀 Sending polls..."
    )

    progress_message = None

    try:
        target_chat = await context.bot.get_chat(
            target_chat_id
        )

        if not await is_target_chat_admin_or_owner(
            target_chat,
            query.from_user.id
        ):
            target_name = "Channel" if target_chat.type == "channel" else "Group"
            await query.answer(
                f"❌ Only the {target_name} Admin or Owner can send polls to this {target_name}.",
                show_alert=True
            )
            return

        total = len(questions)
        sent_count = 0
        failed_items = []

        # Channels should use anonymous polls.
        # Groups/supergroups can use non-anonymous polls.
        is_channel = target_chat.type == "channel"
        is_anonymous = True if is_channel else False

        try:
            progress_message = await query.message.reply_text(
                "📤 <b>Sending Polls...</b>\n\n"
                f"0/{total}",
                parse_mode="HTML"
            )
        except TelegramError:
            progress_message = None

        for index, q in enumerate(questions, start=1):
            try:
                question_text = str(
                    q.get("question", "")
                ).strip()

                options = [
                    str(option).strip()
                    for option in q.get("options", [])
                ]

                correct_index = int(
                    q.get("correct", -1)
                )

                explanation = str(
                    q.get("explanation", "")
                ).strip()

                # Final safety checks before Telegram API.
                if not question_text:
                    raise ValueError(
                        "Question is empty."
                    )

                if not (2 <= len(options) <= 12):
                    raise ValueError(
                        "Poll must have 2-12 options."
                    )

                if not (
                    0 <= correct_index < len(options)
                ):
                    raise ValueError(
                        "The correct option index is invalid."
                    )

                if len(question_text) > 300:
                    raise ValueError(
                        "Question is longer than 300 characters."
                    )

                if any(
                    not option or len(option) > 100
                    for option in options
                ):
                    raise ValueError(
                        "An option is empty or longer than 100 characters."
                    )

                if len(explanation) > 200:
                    explanation = explanation[:200]

                # Native Telegram Quiz Poll.
                # correct_option_ids is the current Bot API/PTB field.
                await send_poll_with_rate_limit(
                    context,
                    target_chat_id,
                    question_text,
                    options,
                    correct_index,
                    explanation if explanation else None,
                    timer=None,
                    is_anonymous=is_anonymous,
                    publish_mode=True
                )

                sent_count += 1

                # Keep a 5-second gap between published polls so Telegram
                # API requests are paced instead of sent in a burst.
                if index < total:
                    await asyncio.sleep(5.0)

            except RetryAfter as e:
                # send_poll helper normally handles RetryAfter,
                # but keep this as an extra safety layer.
                await asyncio.sleep(
                    float(e.retry_after) + 1.0
                )

                try:
                    await send_poll_with_rate_limit(
                        context,
                        target_chat_id,
                        question_text,
                        options,
                        correct_index,
                        explanation if explanation else None,
                        timer=None,
                        is_anonymous=is_anonymous,
                        publish_mode=True
                    )
                    sent_count += 1

                    # Keep a 5-second gap between published polls so Telegram
                    # API requests are paced instead of sent in a burst.
                    if index < total:
                        await asyncio.sleep(5.0)

                except Exception as retry_error:
                    logger.exception(
                        "Retry publish failed at %s",
                        index
                    )
                    failed_items.append(
                        (index, str(retry_error))
                    )

            except Exception as e:
                logger.exception(
                    "Poll publish failed at %s",
                    index
                )

                failed_items.append(
                    (index, str(e))
                )

            # Progress message every 5 polls, first, and last.
            if (
                progress_message
                and (
                    index == 1
                    or index == total
                    or index % 5 == 0
                )
            ):
                try:
                    failed_so_far = len(failed_items)

                    await progress_message.edit_text(
                        "📤 <b>Sending Polls...</b>\n\n"
                        f"✅ Sent: {sent_count}/{total}\n"
                        f"❌ Failed: {failed_so_far}/{total}",
                        parse_mode="HTML"
                    )
                except TelegramError:
                    pass

        if progress_message:
            try:
                await progress_message.edit_text(
                    "🎉 <b>Poll Publishing Complete!</b>\n\n"
                    f"📋 Total: {total}\n"
                    f"✅ Sent: {sent_count}\n"
                    f"❌ Failed: {len(failed_items)}",
                    parse_mode="HTML"
                )
            except TelegramError:
                pass

        if failed_items:
            preview = "\n".join(
                f"• Q{item[0]}: {safe_html(item[1])[:120]}"
                for item in failed_items[:10]
            )

            await query.message.reply_text(
                "⚠️ <b>Some polls could not be sent.</b>\n\n"
                f"{preview}",
                parse_mode="HTML"
            )

    except TelegramError as e:
        logger.exception("Publish target error.")

        await query.message.reply_text(
            "❌ Poll publishing stopped because the target "
            "returned a Telegram error:\n\n"
            f"{safe_html(str(e))}",
            parse_mode="HTML"
        )

    finally:
        context.user_data["publishing_polls"] = False


# ==========================================
# 13. TELEGRAM POLL SENDER
# ==========================================
async def send_poll_with_rate_limit(
    context,
    chat_id,
    question,
    options,
    correct_index,
    explanation,
    timer=None,
    retries=5,
    is_anonymous=False,
    publish_mode=False
):
    async with telegram_rate_limiter:
        # Small spacing prevents bursts.
        await asyncio.sleep(
            0.08 if publish_mode else 0.04
        )

        for attempt in range(retries):
            try:
                poll_kwargs = {
                    "chat_id": chat_id,
                    "question": question,
                    "options": options,
                    "type": Poll.QUIZ,
                    "correct_option_ids": [correct_index],
                    "allows_multiple_answers": False,
                    "is_anonymous": is_anonymous,
                    "allows_revoting": False,
                }

                if explanation:
                    poll_kwargs["explanation"] = explanation

                # Existing live quiz uses timed polls.
                if timer is not None:
                    poll_kwargs["open_period"] = max(
                        5,
                        int(timer)
                    )

                return await context.bot.send_poll(
                    **poll_kwargs
                )

            except RetryAfter as e:
                wait_seconds = float(
                    e.retry_after
                ) + 0.75

                logger.warning(
                    "Telegram rate limit. Waiting %.2fs",
                    wait_seconds
                )

                await asyncio.sleep(
                    wait_seconds
                )

            except (TimedOut, NetworkError) as e:
                logger.warning(
                    "Telegram network error attempt %s/%s: %s",
                    attempt + 1,
                    retries,
                    e
                )

                if attempt < retries - 1:
                    await asyncio.sleep(
                        min(2 ** attempt, 8)
                    )
                else:
                    raise

            except TelegramError:
                raise


# ==========================================
# 14. CALLBACK HANDLER
# ==========================================
async def button_handler(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    query = update.callback_query
    data = query.data

    if data == "schedule_quiz":
        if query.message.chat.type != "private":
            await query.answer("Please use Schedule from private chat.", show_alert=True)
            return
        await query.answer()
        # Reuse the exact loaded quiz/settings already shown in the private card.
        if not context.user_data.get("questions"):
            await query.message.reply_text("❌ Load a saved quiz first from /quizzes.")
            return
        context.user_data["schedule_flow"] = {"stage": "target"}
        await query.message.reply_text(
            "📅 <b>Schedule Quiz</b>\n\n"
            f"🧠 Quiz: <b>{safe_html(context.user_data.get('quiz_title','Quiz'))}</b>\n\n"
            "Send the target group <b>username or public link</b>.\n"
            "Example: <code>@myquizgroup</code> or <code>https://t.me/myquizgroup</code>",
            parse_mode="HTML"
        )
        return

    if data == "schedule_list":
        await query.answer()
        if query.message.chat.type != "private":
            return
        rows = await db_pool.fetch(
            "SELECT id, quiz_title, target_username, scheduled_at FROM quiz_schedules WHERE owner_id=$1 AND status='pending' ORDER BY scheduled_at ASC LIMIT 20",
            query.from_user.id
        )
        if not rows:
            await query.message.reply_text("📅 No pending schedules.")
            return
        buttons=[]
        text=["📅 <b>My Schedules</b>", ""]
        for r in rows:
            text.append(f"🧠 <b>{safe_html(r['quiz_title'])}</b>\n👥 {safe_html(r['target_username'] or str(r['id']))}\n🕐 {format_schedule_ist(r['scheduled_at'])}")
            buttons.append([InlineKeyboardButton("❌ Cancel", callback_data=f"schedule_cancel_private_{r['id']}")])
        await query.message.reply_text("\n\n".join(text), parse_mode="HTML", reply_markup=InlineKeyboardMarkup(buttons))
        return

    if data.startswith("schedule_cancel_private_"):
        await query.answer()
        schedule_id = int(data.rsplit("_",1)[-1])
        row = await db_pool.fetchrow("SELECT target_chat_id FROM quiz_schedules WHERE id=$1", schedule_id)
        target_chat = None
        if row:
            try:
                target_chat = await context.bot.get_chat(int(row["target_chat_id"]))
            except TelegramError:
                target_chat = None
        ok, msg = await cancel_schedule(schedule_id, query.from_user.id, target_chat)
        await query.message.reply_text(("✅ " if ok else "❌ ") + msg)
        return

    if data.startswith("schedule_cancel_"):
        schedule_id = int(data.rsplit("_",1)[-1])
        target_chat = query.message.chat if query.message.chat.type in ["group", "supergroup"] else None
        ok, msg = await cancel_schedule(schedule_id, query.from_user.id, target_chat)
        if not ok:
            await query.answer("❌ " + msg, show_alert=True)
            return
        await query.answer("Schedule cancelled.")
        try:
            await query.edit_message_text("❌ <b>Schedule Cancelled</b>", parse_mode="HTML")
        except TelegramError:
            pass
        return

    # Resume
    if data.startswith("resume_quiz_"):
        await resume_quiz_callback(
            update,
            context
        )
        return

    # Create
    if data == "create":
        if query.message.chat.type != "private":
            await query.answer(
                "Please use private chat.",
                show_alert=True
            )
            return

        await query.answer()

        context.user_data.clear()
        context.user_data["owner_id"] = (
            query.from_user.id
        )
        context.user_data["waiting_title"] = True
        context.user_data["temp_questions"] = []

        await query.edit_message_text(
            "📝 <b>Send Your Quiz Title</b>",
            parse_mode="HTML"
        )
        return

    # My quizzes
    if data == "my_quizzes":
        await query.answer()

        await show_my_quizzes(
            query,
            context
        )
        return

    # Help
    if data == "help":
        await query.answer()

        help_text = (
            "📖 <b>Quiz Bot Help</b>\n\n"
            "• /start - Start the bot\n"
            "• /create - Create a new quiz\n"
            "• /quizzes - My saved quizzes\n"
            "• /done - Finish questions\n"
            "• /stop /pause - Pause quiz\n"
            "• /cancel - Cancel quiz\n"
            "• /resetquiz - Reset quiz\n\n"
            "<b>Correct answer:</b> Use only <code>✅</code>\n\n"
            "📤 Share Polls sends questions as "
            "native Telegram Quiz Polls to "
            "a Channel/Group."
        )

        await query.edit_message_text(
            help_text,
            parse_mode="HTML"
        )
        return

    # Back
    if data == "back_start":
        await query.answer()

        await query.edit_message_text(
            "🤖 <b>ENTERPRISE HIGH-SCALE QUIZ BOT</b>",
            parse_mode="HTML",
            reply_markup=build_start_keyboard()
        )
        return

    # Delete
    if data.startswith("del_"):
        try:
            quiz_id = int(
                data.split("_", 1)[1]
            )
        except ValueError:
            await query.answer(
                "❌ Invalid quiz.",
                show_alert=True
            )
            return

        deleted = await delete_quiz_async(
            query.from_user.id,
            quiz_id
        )

        if deleted:
            await query.answer(
                "🗑 Quiz Deleted!",
                show_alert=True
            )

            await show_my_quizzes(
                query,
                context
            )
        else:
            await query.answer(
                "❌ Failed to delete.",
                show_alert=True
            )

        return

    # Load
    if data.startswith("load_"):
        code = data.split(
            "_",
            1
        )[1]

        loaded = await load_quiz_by_code_or_id(
            code
        )

        if not loaded:
            await query.answer(
                "❌ Quiz not found.",
                show_alert=True
            )
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

        share_link = (
            f"@{BOT_USERNAME} quiz:{short_code}"
        )

        await query.edit_message_text(
            f"👍 Loaded: <b>{safe_html(title)}</b>\n"
            f"📋 Questions: {len(questions)}\n\n"
            f"Share Code:\n"
            f"<code>{safe_html(share_link)}</code>",
            parse_mode="HTML",
            reply_markup=build_settings_keyboard(
                context.user_data
            )
        )
        return

    # Start publishing
    if data == "publish_polls":
        if query.message.chat.type != "private":
            await query.answer(
                "📤 Please use Share Polls from a private chat.",
                show_alert=True
            )
            return

        await start_publish_polls(
            query,
            context
        )
        return

    # Confirm publishing
    if data == "confirm_publish_polls":
        if query.message.chat.type != "private":
            await query.answer(
                "❌ Please use private chat.",
                show_alert=True
            )
            return

        await publish_all_polls(
            query,
            context
        )
        return

    # Change publish target
    if data == "change_publish_target":
        context.user_data["waiting_publish_target"] = True
        context.user_data["publish_target"] = None
        context.user_data["publish_target_raw"] = None

        await query.answer()

        await query.message.reply_text(
            "🔄 <b>Send a New Target</b>\n\n"
            "🔗 Public Link\n"
            "👤 @username\n"
            "🆔 Chat ID\n\n"
            "Example:\n"
            "<code>@mychannel</code>",
            parse_mode="HTML",
            reply_markup=build_publish_target_keyboard()
        )
        return

    # Cancel publishing
    if data == "cancel_publish":
        context.user_data["waiting_publish_target"] = False
        context.user_data["publish_target"] = None
        context.user_data["publish_target_raw"] = None

        await query.answer(
            "❌ Publishing cancelled."
        )

        await query.message.reply_text(
            "❌ Poll publishing cancelled."
        )
        return

    # Cancel creation
    if data == "cancel_creation":
        context.user_data.clear()

        await query.answer(
            "❌ Creation cancelled."
        )

        await query.edit_message_text(
            "❌ <b>Quiz creation cancelled.</b>",
            parse_mode="HTML",
            reply_markup=build_start_keyboard()
        )
        return

    # Finish creation
    if data == "finish_creation":
        if query.message.chat.type != "private":
            await query.answer(
                "Please use private chat.",
                show_alert=True
            )
            return

        questions = context.user_data.get(
            "temp_questions",
            []
        )

        if not questions:
            await query.answer(
                "❌ No questions added.",
                show_alert=True
            )
            return

        await query.answer(
            "💾 Saving quiz..."
        )

        try:
            saved = await save_current_quiz(
                query.from_user.id,
                context
            )
        except Exception:
            logger.exception(
                "Quiz save failed from callback."
            )

            await query.message.reply_text(
                "❌ Failed to save quiz. Try again later."
            )
            return

        _, short_code, title, questions = saved

        share_link = (
            f"@{BOT_USERNAME} quiz:{short_code}"
        )

        await query.edit_message_text(
            f"✅ <b>Quiz Created Successfully!</b>\n\n"
            f"📌 Title: <b>{safe_html(title)}</b>\n"
            f"📋 Questions: {len(questions)}\n\n"
            f"Share Code:\n"
            f"<code>{safe_html(share_link)}</code>",
            parse_mode="HTML",
            reply_markup=build_settings_keyboard(
                context.user_data
            )
        )
        return

    # Settings
    if data == "toggle_qshuffle":
        context.user_data["qshuffle"] = not context.user_data.get(
            "qshuffle",
            False
        )

        await query.answer()

    elif data == "toggle_oshuffle":
        context.user_data["oshuffle"] = not context.user_data.get(
            "oshuffle",
            False
        )

        await query.answer()

    elif data == "toggle_exp":
        context.user_data["explanation"] = not context.user_data.get(
            "explanation",
            True
        )

        await query.answer()

    elif data.startswith("set_timer_"):
        timer_val = int(
            data.split("_")[-1]
        )

        context.user_data["timer"] = timer_val

        await query.answer(
            f"Timer set to {timer_val}s"
        )

    elif data == "start_quiz":
        await query.answer()

        await begin_quiz(
            query.message.chat_id,
            context
        )
        return

    try:
        await query.edit_message_reply_markup(
            reply_markup=build_settings_keyboard(
                context.user_data
            )
        )
    except TelegramError:
        pass


# ==========================================
# 15. TEXT INPUT HANDLER
# ==========================================
async def receive_text(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    if update.effective_chat.type != "private":
        return

    text = update.message.text.strip()

    if await process_schedule_text(update, context, text):
        return

    # Publish target input must be checked before
    # question/title states.
    if context.user_data.get(
        "waiting_publish_target"
    ):
        await verify_and_prepare_publish(
            update,
            context,
            text
        )
        return

    # Quiz title
    if context.user_data.get("waiting_title"):
        title = text

        if not title or len(title) > 200:
            await update.message.reply_text(
                "❌ Title cannot be empty or longer than 200 chars."
            )
            return

        context.user_data["quiz_title"] = title
        context.user_data["waiting_title"] = False
        context.user_data["waiting_questions"] = True
        context.user_data["temp_questions"] = []

        await update.message.reply_text(
            "📝 <b>Now Send Your Questions</b>\n\n"
            "Use only <code>✅</code> for the correct answer.\n\n"
            "Example:\n\n"
            "<code>Q1. What is the capital of India?\n"
            "A. Mumbai\n"
            "B. Kolkata\n"
            "C. ✅ New Delhi\n"
            "D. Chennai</code>\n\n"
            "You can send multiple questions in one batch.",
            parse_mode="HTML"
        )
        return

    # Question input
    if context.user_data.get("waiting_questions"):
        questions, skipped = parse_questions_flexible(
            update.message.text
        )

        if not questions:
            await update.message.reply_text(
                "❌ No valid question format was found.\n\n"
                "Each question must contain exactly one <code>✅</code> "
                "on the correct option. for the correct answer.",
                parse_mode="HTML"
            )
            return

        current_list = context.user_data.get(
            "temp_questions",
            []
        )

        if len(current_list) + len(questions) > 1000:
            await update.message.reply_text(
                "⚠️ Maximum limit is 1000 questions per quiz."
            )
            return

        current_list.extend(questions)

        context.user_data["temp_questions"] = current_list

        skip_msg = (
            f"\n⚠️ Skipped {skipped} invalid item(s)."
            if skipped > 0
            else ""
        )

        await update.message.reply_text(
            f"✅ <b>{len(questions)} Questions Added!</b>"
            f"{skip_msg}\n"
            f"📊 Total So Far: "
            f"<b>{len(current_list)}</b>\n\n"
            "Send more questions or press "
            "<b>Done Adding Questions</b>.",
            parse_mode="HTML",
            reply_markup=build_creation_done_keyboard()
        )


# ==========================================
# 16. LIVE QUIZ ENGINE
# ==========================================
async def begin_quiz(
    chat_id: int,
    context: ContextTypes.DEFAULT_TYPE,
    schedule_id: int = None
):
    chat_key = str(chat_id)

    lock = redis_client.lock(
        f"lock:quiz_start:{chat_key}",
        timeout=10
    )

    acquired = await lock.acquire(
        blocking=False
    )

    if not acquired:
        await context.bot.send_message(
            chat_id,
            "⚠️ Quiz initialization in progress..."
        )
        return

    try:
        active = await redis_client.get(
            f"quiz_active:{chat_key}"
        )

        if active:
            await context.bot.send_message(
                chat_id,
                "⚠️ A quiz is already running in this chat."
            )
            return

        source = context.user_data
        questions = deepcopy(source.get("questions", []))

        if not questions:
            await context.bot.send_message(
                chat_id,
                "❌ No questions found in quiz."
            )
            return

        qshuffle = source.get("qshuffle", False)
        oshuffle = source.get("oshuffle", False)
        explanation_enable = source.get("explanation", True)
        timer = source.get("timer", 20)
        title = source.get("quiz_title", "Quiz")
        owner_id = source.get("owner_id", 0)
        quiz_id = source.get("quiz_id", 0)

        session_id = uuid.uuid4().hex

        if qshuffle:
            random.shuffle(questions)

        is_private = chat_id > 0

        await redis_client.set(
            f"quiz_active:{chat_key}",
            "1",
            ex=86400
        )

        await redis_client.hset(
            f"quiz_state:{chat_key}",
            mapping={
                "owner_id": owner_id,
                "quiz_id": quiz_id,
                "schedule_id": schedule_id or "",
                "session_id": session_id,
                "title": title,
                "timer": timer,
                "is_private": "1" if is_private else "0",
                "total_q": len(questions),
                "oshuffle": "1" if oshuffle else "0",
                "explanation": "1" if explanation_enable else "0",
                "questions": json.dumps(questions, ensure_ascii=False)
            }
        )

        context.user_data["active_quiz_questions"] = deepcopy(questions)
        context.user_data["active_oshuffle"] = oshuffle
        context.user_data["active_explanation"] = explanation_enable

        await redis_client.set(
            f"quiz_index:{chat_key}",
            "1",
            ex=86400
        )
        await redis_client.delete(
            f"quiz_cancelled:{chat_key}",
            f"quiz_reset:{chat_key}",
            f"quiz_stop:{chat_key}",
            f"quiz_pause:{chat_key}",
            f"quiz_current_poll:{chat_key}"
        )

        await context.bot.send_message(
            chat_id,
            f"🚀 <b>Quiz starting in 5 seconds...</b>\n\n"
            f"📚 Title: <b>{safe_html(title)}</b>\n"
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
                timer=timer,
                session_id=session_id
            )
        )

        track_task(task)

    finally:
        try:
            await lock.release()
        except Exception:
            pass


async def run_quiz_loop(
    chat_key: str,
    chat_id: int,
    questions: list,
    context: ContextTypes.DEFAULT_TYPE,
    oshuffle: bool,
    explanation_enable: bool,
    timer: int,
    start_index: int = 1,
    session_id: str = None
):
    total_questions = len(questions)
    paused_exit = False
    reset_exit = False
    completed_or_stopped = False
    current_poll_message_id = None

    try:
        if not session_id:
            session_id = await redis_client.hget(
                f"quiz_state:{chat_key}",
                "session_id"
            )

        if not session_id:
            raise RuntimeError(
                "Active quiz session_id is missing."
            )

        index = max(1, int(start_index))

        while index <= total_questions:
            state = await redis_client.hgetall(
                f"quiz_state:{chat_key}"
            )

            if not state:
                raise RuntimeError(
                    "Active quiz state disappeared."
                )

            if state.get("session_id") != session_id:
                logger.warning(
                    "Quiz session changed; stopping old quiz loop. chat=%s",
                    chat_key
                )
                return

            if await redis_client.get(
                f"quiz_reset:{chat_key}"
            ):
                reset_exit = True
                return

            if await redis_client.get(
                f"quiz_pause:{chat_key}"
            ):
                paused_exit = True
                return

            if await redis_client.get(
                f"quiz_stop:{chat_key}"
            ):
                completed_or_stopped = True
                break

            if not await redis_client.get(
                f"quiz_active:{chat_key}"
            ):
                logger.warning(
                    "Quiz active flag missing; stopping loop. chat=%s",
                    chat_key
                )
                return

            q = questions[index - 1]
            options = list(q["options"])
            correct_index = int(q["correct"])

            if oshuffle:
                indexed = list(enumerate(options))
                random.shuffle(indexed)

                options = [
                    opt
                    for _, opt in indexed
                ]

                correct_index = next(
                    n
                    for n, (original_index, _) in enumerate(indexed)
                    if original_index == q["correct"]
                )

            explanation = (
                q.get("explanation")
                if explanation_enable
                else None
            )

            try:
                poll_msg = await send_poll_with_rate_limit(
                    context,
                    chat_id,
                    f"[{index}/{total_questions}] "
                    f"{q['question']}",
                    options,
                    correct_index,
                    explanation,
                    timer=timer,
                    is_anonymous=False,
                    publish_mode=False
                )
            except Exception as exc:
                logger.exception(
                    "Poll delivery failed. chat=%s question=%s",
                    chat_key,
                    index
                )
                try:
                    await context.bot.send_message(
                        chat_id,
                        "❌ Quiz stopped because the next question "
                        "could not be sent. Please start the quiz again."
                    )
                except TelegramError:
                    pass
                return

            current_poll_message_id = poll_msg.message_id
            poll_id = poll_msg.poll.id

            await redis_client.hset(
                f"quiz_current_poll:{chat_key}",
                mapping={
                    "message_id": poll_msg.message_id,
                    "poll_id": poll_id
                }
            )

            await redis_client.set(
                f"quiz_index:{chat_key}",
                str(index),
                ex=86400
            )

            q_start_time = time.time()

            await redis_client.set(
                f"poll_mapping:{poll_id}",
                json.dumps({
                    "chat_key": chat_key,
                    "session_id": session_id,
                    "correct": correct_index,
                    "start_time": q_start_time
                }),
                ex=86400
            )

            is_private = chat_id > 0
            wait_time = 0.0
            advance_now = False

            while wait_time < timer:
                # If a new session replaced this one, never continue.
                live_session = await redis_client.hget(
                    f"quiz_state:{chat_key}",
                    "session_id"
                )
                if live_session != session_id:
                    logger.warning(
                        "Session changed while waiting. chat=%s",
                        chat_key
                    )
                    return

                if await redis_client.get(
                    f"quiz_reset:{chat_key}"
                ):
                    reset_exit = True
                    try:
                        await context.bot.stop_poll(
                            chat_id,
                            poll_msg.message_id
                        )
                    except TelegramError:
                        pass
                    return

                if await redis_client.get(
                    f"quiz_stop:{chat_key}"
                ):
                    completed_or_stopped = True
                    try:
                        await context.bot.stop_poll(
                            chat_id,
                            poll_msg.message_id
                        )
                    except TelegramError:
                        pass
                    break

                if await redis_client.get(
                    f"quiz_pause:{chat_key}"
                ):
                    paused_exit = True
                    try:
                        await context.bot.stop_poll(
                            chat_id,
                            poll_msg.message_id
                        )
                    except TelegramError:
                        pass
                    return

                if (
                    is_private
                    and await redis_client.get(
                        f"quiz_next:{chat_key}"
                    )
                ):
                    await redis_client.delete(
                        f"quiz_next:{chat_key}"
                    )
                    advance_now = True
                    break

                await asyncio.sleep(0.5)
                wait_time += 0.5

            await redis_client.delete(
                f"quiz_current_poll:{chat_key}",
                f"poll_mapping:{poll_id}"
            )

            current_poll_message_id = None

            if reset_exit or paused_exit:
                return

            # If stopped, finish_quiz() will see quiz_cancelled when
            # /cancel was used; /stop simply produces the current results.
            if completed_or_stopped:
                break

            # Poll naturally timed out or a private answer requested the
            # next question early. Move to the next question.
            index += 1
            await redis_client.set(
                f"quiz_index:{chat_key}",
                str(index),
                ex=86400
            )

            # Keep the same UX as the original Live Quiz:
            # after a private answer, wait 2 second before sending
            # the next question. This also prevents a burst of polls
            # from being generated immediately after an answer.
            await asyncio.sleep(2.0)

        completed_or_stopped = True

    except asyncio.CancelledError:
        logger.info(
            "Quiz task cancelled. chat=%s",
            chat_key
        )
        raise

    except Exception:
        logger.exception(
            "Unexpected LIVE QUIZ ENGINE failure. chat=%s",
            chat_key
        )

        # Do NOT call finish_quiz() here. A runtime error must never
        # masquerade as a normal zero-candidate result.
        try:
            if current_poll_message_id is not None:
                await context.bot.stop_poll(
                    chat_id,
                    current_poll_message_id
                )
        except TelegramError:
            pass

        try:
            await context.bot.send_message(
                chat_id,
                "❌ A quiz engine error occurred and the quiz was stopped. "
                "Please start the quiz again."
            )
        except TelegramError:
            pass

        return

    finally:
        if completed_or_stopped and not paused_exit and not reset_exit:
            try:
                await finish_quiz(
                    chat_key,
                    context,
                    chat_id=chat_id
                )
            except Exception:
                logger.exception(
                    "Failed to finish quiz. chat=%s",
                    chat_key
                )



# ==========================================
# 17. POLL ANSWER / SCORE
# ==========================================
async def poll_answer_handler(
    update: Update,
    context: ContextTypes.DEFAULT_TYPE
):
    answer = update.poll_answer

    if not answer:
        return

    poll_id = answer.poll_id
    user = answer.user

    if not user:
        return

    raw_poll_data = await redis_client.get(
        f"poll_mapping:{poll_id}"
    )

    if not raw_poll_data:
        return

    pdata = json.loads(
        raw_poll_data
    )

    chat_key = pdata["chat_key"]
    mapping_session_id = pdata.get("session_id")

    # Ignore late answers belonging to an older quiz session.
    current_state = await redis_client.hgetall(
        f"quiz_state:{chat_key}"
    )
    if not current_state:
        return

    if mapping_session_id:
        if mapping_session_id != current_state.get("session_id"):
            return

    if await redis_client.get(f"quiz_cancelled:{chat_key}"):
        return

    if not await redis_client.get(f"quiz_active:{chat_key}"):
        return

    correct_option = int(
        pdata["correct"]
    )

    q_start_time = float(
        pdata["start_time"]
    )

    # First answer wins.
    first_answer = await redis_client.set(
        f"answered:{poll_id}:{user.id}",
        "1",
        nx=True,
        ex=7200
    )

    if not first_answer:
        return

    time_taken = max(
        0.1,
        time.time() - q_start_time
    )

    user_name = user.full_name

    await redis_client.hset(
        f"participants:{chat_key}",
        str(user.id),
        user_name
    )

    if (
        answer.option_ids
        and answer.option_ids[0] == correct_option
    ):
        await redis_client.hincrby(
            f"scores:{chat_key}",
            str(user.id),
            1
        )

    await redis_client.hincrbyfloat(
        f"times:{chat_key}",
        str(user.id),
        time_taken
    )

    score = int(
        await redis_client.hget(
            f"scores:{chat_key}",
            str(user.id)
        )
        or 0
    )

    total_time = float(
        await redis_client.hget(
            f"times:{chat_key}",
            str(user.id)
        )
        or 0.0
    )

    composite_rank = (
        (score * 1000000)
        - min(total_time, 999999.0)
    )

    await redis_client.zadd(
        f"leaderboard:{chat_key}",
        {
            str(user.id): composite_rank
        }
    )

    # Private quiz: next question can start quickly.
    try:
        chat_id = int(chat_key)

        if chat_id > 0:
            await redis_client.set(
                f"quiz_next:{chat_key}",
                "1",
                ex=60
            )

    except ValueError:
        pass


# ==========================================
# 18. FINISH QUIZ / RESULTS
# ==========================================
async def finish_quiz(
    chat_key: str,
    context: ContextTypes.DEFAULT_TYPE,
    chat_id: int = None
):
    lock = redis_client.lock(
        f"lock:finish:{chat_key}",
        timeout=30
    )

    acquired = await lock.acquire(
        blocking=False
    )

    if not acquired:
        return

    try:
        target_chat_id = (
            chat_id
            if chat_id is not None
            else int(chat_key)
        )

        quiz_info = await redis_client.hgetall(
            f"quiz_state:{chat_key}"
        )

        title = quiz_info.get(
            "title",
            "Quiz"
        )

        total_q = int(
            quiz_info.get(
                "total_q",
                0
            )
        )

        participants = await redis_client.hgetall(
            f"participants:{chat_key}"
        )

        scores = await redis_client.hgetall(
            f"scores:{chat_key}"
        )

        times = await redis_client.hgetall(
            f"times:{chat_key}"
        )

        total_candidates = len(
            participants
        )

        cancelled = bool(
            await redis_client.get(
                f"quiz_cancelled:{chat_key}"
            )
        )

        if cancelled:
            pass

        elif total_candidates == 0:
            msg = (
                f"📌 {safe_html(title)}\n\n"
                "🏆 QUIZ RESULT\n"
                "━━━━━━━━━━━━\n"
                "👥 Total Candidates: 0\n"
                "━━━━━━━━━━━━\n\n"
                "Nobody participated in this quiz."
            )

            try:
                await context.bot.send_message(
                    target_chat_id,
                    msg,
                    parse_mode="HTML"
                )
            except TelegramError:
                pass

        else:
            ranked_users = await redis_client.zrevrange(
                f"leaderboard:{chat_key}",
                0,
                -1,
                withscores=False
            )

            leaderboard = []

            for uid in ranked_users:
                name = participants.get(
                    uid,
                    "User"
                )

                sc = int(
                    scores.get(
                        uid,
                        0
                    )
                )

                tm = float(
                    times.get(
                        uid,
                        0.0
                    )
                )

                leaderboard.append(
                    (
                        int(uid),
                        name,
                        sc,
                        tm
                    )
                )

            await persist_results_to_db(
                chat_key,
                leaderboard
            )

            header = (
                f"📌 {safe_html(title)}\n\n"
                "🏆 QUIZ RESULT\n"
                "━━━━━━━━━━━━\n"
                f"👥 Total Candidates: {total_candidates}\n"
                "━━━━━━━━━━━━\n\n"
            )

            medals = [
                "🥇",
                "🥈",
                "🥉"
            ]

            chunk = header

            for idx, (
                uid,
                name,
                score,
                t_secs
            ) in enumerate(leaderboard):

                rank_str = (
                    medals[idx]
                    if idx < 3
                    else f"{idx + 1}."
                )

                formatted_t = format_time(
                    t_secs
                )

                line = (
                    f"{rank_str} {safe_html(name)}\n"
                    f"🎯 Score : {score}/{total_q}\n"
                    f"⏱️ Time  : {formatted_t}\n\n"
                )

                if (
                    idx == 2
                    and total_candidates > 3
                ):
                    line += (
                        "━━━━━━━━━━━━\n\n"
                    )

                if (
                    len(chunk) + len(line)
                    > MAX_TELEGRAM_MSG_LEN
                ):
                    try:
                        await context.bot.send_message(
                            target_chat_id,
                            chunk,
                            parse_mode="HTML"
                        )
                    except TelegramError:
                        pass

                    chunk = line
                else:
                    chunk += line

            top_ranker_name = (
                leaderboard[0][1]
                if leaderboard
                else "None"
            )

            footer = (
                "━━━━━━━━━━━━\n\n"
                f"🔥 Top Ranker: "
                f"{safe_html(top_ranker_name)}"
            )

            if (
                len(chunk) + len(footer)
                > MAX_TELEGRAM_MSG_LEN
            ):
                try:
                    await context.bot.send_message(
                        target_chat_id,
                        chunk,
                        parse_mode="HTML"
                    )
                except TelegramError:
                    pass

                chunk = footer

            else:
                chunk += footer

            try:
                await context.bot.send_message(
                    target_chat_id,
                    chunk,
                    parse_mode="HTML"
                )
            except TelegramError:
                pass

        await redis_client.delete(
            f"quiz_active:{chat_key}",
            f"quiz_state:{chat_key}",
            f"quiz_stop:{chat_key}",
            f"quiz_pause:{chat_key}",
            f"quiz_next:{chat_key}",
            f"quiz_index:{chat_key}",
            f"quiz_current_poll:{chat_key}",
            f"quiz_cancelled:{chat_key}",
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


async def persist_results_to_db(
    chat_key: str,
    leaderboard: list
):
    if not db_pool:
        return

    try:
        chat_id = int(chat_key)

        quiz_info = await redis_client.hgetall(
            f"quiz_state:{chat_key}"
        )

        quiz_id = int(
            quiz_info.get(
                "quiz_id"
            )
            or 0
        )

        quiz_id_val = (
            quiz_id
            if quiz_id > 0
            else None
        )

        async with db_pool.acquire() as conn:
            async with conn.transaction():
                for (
                    uid,
                    name,
                    score,
                    t_secs
                ) in leaderboard:

                    await conn.execute(
                        """
                        INSERT INTO quiz_results
                        (quiz_id, chat_id, user_id,
                         user_name, score, total_time)
                        VALUES ($1, $2, $3, $4, $5, $6)
                        """,
                        quiz_id_val,
                        chat_id,
                        uid,
                        name,
                        score,
                        t_secs
                    )

        logger.info(
            "✅ Quiz results persisted for chat %s",
            chat_key
        )

    except Exception as e:
        logger.error(
            "❌ DB Batch Persistence Error: %s",
            e
        )


# ==========================================
# 19. LIFECYCLE
# ==========================================
async def acquire_single_instance_lock():
    """Ensure only one process for this bot token can poll Telegram.

    Telegram allows only one long-polling getUpdates consumer per bot token.
    A PostgreSQL advisory lock gives Render restart/duplicate-process protection
    without requiring another service or changing the user-facing schedule flow.
    """
    global instance_lock_conn

    if not db_pool:
        raise RuntimeError("Database pool is not initialized.")

    instance_lock_conn = await db_pool.acquire()
    lock_key = BOT_TOKEN or "quiz-bot"
    acquired = await instance_lock_conn.fetchval(
        "SELECT pg_try_advisory_lock(hashtextextended($1, 0))",
        lock_key
    )
    if not acquired:
        await db_pool.release(instance_lock_conn)
        instance_lock_conn = None
        raise RuntimeError(
            "Another QuizBot process is already running with this BOT_TOKEN. "
            "Only one polling instance is allowed."
        )

    logger.info("🔒 Single-instance Telegram lock acquired.")


async def release_single_instance_lock():
    global instance_lock_conn
    if instance_lock_conn is None:
        return
    try:
        await instance_lock_conn.execute(
            "SELECT pg_advisory_unlock(hashtextextended($1, 0))",
            BOT_TOKEN or "quiz-bot"
        )
    except Exception:
        logger.exception("Failed to release Telegram instance lock.")
    finally:
        if db_pool:
            try:
                await db_pool.release(instance_lock_conn)
            except Exception:
                pass
        instance_lock_conn = None


async def post_init(
    application: Application
):
    global BOT_USERNAME

    bot_info = await application.bot.get_me()

    BOT_USERNAME = bot_info.username

    logger.info(
        "🤖 Bot Username Automatically Detected: @%s",
        BOT_USERNAME
    )

    if not WEBHOOK_URL:
        await start_dummy_server()
    await init_infrastructure()

    # Telegram polling requires exactly one active consumer for this token.
    # Acquire the DB advisory lock before polling starts.
    await acquire_single_instance_lock()

    # Recover schedules that were being processed when the service restarted.
    await recover_running_schedules(application)

    global schedule_worker_task
    schedule_worker_task = asyncio.create_task(schedule_worker(application))
    track_task(schedule_worker_task)

    if WEBHOOK_URL:
        webhook_endpoint = (
            f"{WEBHOOK_URL}/telegram/{BOT_TOKEN}"
        )

        await application.bot.set_webhook(
            url=webhook_endpoint,
            secret_token=WEBHOOK_SECRET,
            allowed_updates=[
                "message",
                "callback_query",
                "poll_answer",
                "inline_query"
            ]
        )

        logger.info(
            "✅ Webhook configured on %s",
            webhook_endpoint
        )


async def post_shutdown(
    application: Application
):
    logger.info(
        "🛑 Executing Graceful Application Shutdown..."
    )

    for task in list(background_tasks):
        task.cancel()

    if background_tasks:
        await asyncio.gather(
            *list(background_tasks),
            return_exceptions=True
        )

    if redis_client:
        try:
            await redis_client.close()
        except Exception:
            pass

    await release_single_instance_lock()

    if db_pool:
        try:
            await db_pool.close()
        except Exception:
            pass

    logger.info(
        "✅ All connections safely closed."
    )


# ==========================================
# 20. POSTCHANNEL COMMAND
# ==========================================
async def postchannel_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """Open the Share Polls target flow for the currently loaded quiz."""
    if update.effective_chat.type != "private":
        await update.message.reply_text("📤 Please use /postchannel only in a private chat.")
        return

    questions = context.user_data.get("questions", [])
    if not questions:
        await update.message.reply_text(
            "❌ Please load or create a quiz before using /postchannel."
        )
        return

    context.user_data["waiting_publish_target"] = True
    context.user_data["publish_target"] = None
    context.user_data["publish_target_raw"] = None

    await update.message.reply_text(
        "📤 <b>Share Polls</b>\n\n"
        "Send one of the following:\n\n"
        "🔗 Public Link: <code>https://t.me/example</code>\n"
        "👤 Username: <code>@example</code>\n"
        "🆔 Chat ID: <code>-1001234567890</code>\n\n"
        f"📋 Total Polls: <b>{len(questions)}</b>",
        parse_mode="HTML",
        reply_markup=build_publish_target_keyboard()
    )


# ==========================================
# 21. MAIN
# ==========================================
def main():
    request = HTTPXRequest(
        connect_timeout=30.0,
        read_timeout=30.0,
        write_timeout=30.0,
        pool_timeout=30.0
    )

    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .request(request)
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    app.add_handler(
        CommandHandler(
            ["start"],
            start_handler
        )
    )

    app.add_handler(
        CommandHandler(
            ["help"],
            help_handler
        )
    )

    app.add_handler(
        CommandHandler(
            ["create", "newquiz"],
            create_command
        )
    )

    app.add_handler(
        CommandHandler(
            ["postchannel", "sharepolls"],
            postchannel_command
        )
    )

    app.add_handler(
        CommandHandler(
            ["done"],
            done_command
        )
    )

    app.add_handler(
        CommandHandler(
            ["stop", "endquiz", "pause"],
            stop_command
        )
    )

    app.add_handler(
        CommandHandler(
            ["cancel", "stopquiz", "kill"],
            cancel_command
        )
    )

    app.add_handler(
        CommandHandler(
            ["resetquiz", "clearquiz", "reset"],
            force_reset_command
        )
    )

    app.add_handler(
        CommandHandler(
            ["schedule"],
            schedule_command
        )
    )

    app.add_handler(
        CommandHandler(
            ["schedules", "myschedules"],
            show_my_schedules
        )
    )

    app.add_handler(
        CommandHandler(
            ["quizzes", "my_quizzes", "myquizzes"],
            show_my_quizzes
        )
    )

    # Specific callback handler FIRST.
    # Generic button_handler handles everything else.
    app.add_handler(
        CallbackQueryHandler(
            button_handler
        )
    )

    app.add_handler(
        InlineQueryHandler(
            inline_query_handler
        )
    )

    app.add_handler(
        MessageHandler(
            filters.TEXT & ~filters.COMMAND,
            receive_text
        )
    )

    app.add_handler(
        PollAnswerHandler(
            poll_answer_handler
        )
    )

    if WEBHOOK_URL:
        app.run_webhook(
            listen="0.0.0.0",
            port=PORT,
            url_path=f"telegram/{BOT_TOKEN}",
            secret_token=WEBHOOK_SECRET,
            webhook_url=(
                f"{WEBHOOK_URL}/telegram/{BOT_TOKEN}"
            ),
            allowed_updates=[
                "message",
                "callback_query",
                "poll_answer",
                "inline_query"
            ]
        )

    else:
        logger.info(
            "⚡ Starting Bot in Polling Mode..."
        )

        app.run_polling(
            drop_pending_updates=True,
            allowed_updates=[
                "message",
                "callback_query",
                "poll_answer",
                "inline_query"
            ]
        )


if __name__ == "__main__":
    main()
