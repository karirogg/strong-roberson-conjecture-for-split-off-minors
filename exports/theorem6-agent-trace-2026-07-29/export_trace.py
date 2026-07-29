#!/usr/bin/env python3
"""Export a sanitized, shareable trace of the Theorem 6 proof task.

The Codex rollout files contain useful action traces mixed with implementation
details that are not suitable for redistribution.  This exporter keeps the
visible conversation, task lifecycle, tool calls and outputs, patch summaries,
and agent-to-agent routing metadata.  It excludes model reasoning records,
system/developer prompts, environment snapshots, and encrypted collaboration
payloads.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import zipfile
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


THREAD_ID = "019fae00-2a41-7863-b12f-aedf7785d675"
PROOF_TURN_ID = "019fae00-2ac1-74e3-ab75-55efd5ce55b1"
DEFAULT_SESSION_DIR = Path.home() / ".codex" / "sessions" / "2026" / "07" / "29"
SCHEMA_VERSION = "1.0.0"

FERNET_RE = re.compile(r"gAAAAA[A-Za-z0-9_-]{40,}")
DROP_KEYS = {
    "base_instructions",
    "dynamic_tools",
    "encrypted_content",
    "internal_chat_message_metadata_passthrough",
    "memory_citation",
}
COLLABORATION_TOOLS = {
    "spawn_agent",
    "followup_task",
    "send_message",
    "interrupt_agent",
}


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open(encoding="utf-8") as handle:
        for line_number, line in enumerate(handle, 1):
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as error:
                raise RuntimeError(f"{path}:{line_number}: {error}") from error
    return rows


class Sanitizer:
    def __init__(self, workspace: Path) -> None:
        self.workspace = str(workspace.resolve())
        self.home = str(Path.home())

    def text(self, value: str) -> str:
        result = value.replace(self.workspace, "${WORKSPACE}")
        result = result.replace(self.home, "${HOME}")
        result = FERNET_RE.sub("<encrypted collaboration payload omitted>", result)
        return result

    def value(self, value: Any) -> Any:
        if isinstance(value, str):
            return self.text(value)
        if isinstance(value, list):
            return [self.value(item) for item in value]
        if isinstance(value, dict):
            return {
                key: self.value(item)
                for key, item in value.items()
                if key not in DROP_KEYS
            }
        return value

    def tool_arguments(self, tool: str, arguments: Any) -> Any:
        parsed = arguments
        if isinstance(arguments, str):
            try:
                parsed = json.loads(arguments)
            except json.JSONDecodeError:
                parsed = arguments
        parsed = self.value(parsed)
        if tool in COLLABORATION_TOOLS and isinstance(parsed, dict):
            if "message" in parsed:
                parsed["message"] = "<encrypted collaboration payload omitted>"
        return parsed


def extract_session_identity(meta: dict[str, Any]) -> tuple[str, str | None]:
    source = meta.get("source")
    if isinstance(source, dict):
        spawn = source.get("subagent", {}).get("thread_spawn", {})
        if spawn:
            return spawn.get("agent_path", "/root/unknown"), spawn.get("agent_nickname")
    return "/root", None


def is_child_of(meta: dict[str, Any], thread_id: str) -> bool:
    source = meta.get("source")
    if not isinstance(source, dict):
        return False
    spawn = source.get("subagent", {}).get("thread_spawn", {})
    return spawn.get("parent_thread_id") == thread_id


def discover_sessions(
    session_dir: Path, thread_id: str
) -> list[tuple[Path, list[dict[str, Any]], dict[str, Any], str, str | None]]:
    discovered = []
    for path in sorted(session_dir.glob("*.jsonl")):
        rows = read_jsonl(path)
        if not rows or rows[0].get("type") != "session_meta":
            continue
        meta = rows[0].get("payload", {})
        if meta.get("id") != thread_id and not is_child_of(meta, thread_id):
            continue
        agent, nickname = extract_session_identity(meta)
        discovered.append((path, rows, meta, agent, nickname))
    if not any(meta.get("id") == thread_id for _, _, meta, _, _ in discovered):
        raise RuntimeError(f"main session {thread_id} not found under {session_dir}")
    return discovered


def event_base(
    row: dict[str, Any],
    session_id: str,
    agent: str,
    sequence: int,
    kind: str,
) -> dict[str, Any]:
    return {
        "timestamp": row.get("timestamp"),
        "session_id": session_id,
        "agent": agent,
        "sequence": sequence,
        "kind": kind,
    }


def own_agent_start(rows: list[dict[str, Any]], proof_turn_id: str) -> int:
    for index, row in enumerate(rows):
        payload = row.get("payload", {})
        if (
            row.get("type") == "event_msg"
            and payload.get("type") == "task_started"
            and payload.get("turn_id") != proof_turn_id
        ):
            return index
    raise RuntimeError("sub-agent session has no own task_started event")


def main_proof_end(rows: list[dict[str, Any]], proof_turn_id: str) -> int:
    for index, row in enumerate(rows):
        payload = row.get("payload", {})
        if (
            row.get("type") == "event_msg"
            and payload.get("type") == "task_complete"
            and payload.get("turn_id") == proof_turn_id
        ):
            return index + 1
    raise RuntimeError(f"proof turn {proof_turn_id} has no task_complete event")


def patch_summary(payload: dict[str, Any], sanitizer: Sanitizer) -> dict[str, Any]:
    changes = []
    for path, detail in payload.get("changes", {}).items():
        item = {
            "path": sanitizer.text(path),
            "change": detail.get("type"),
        }
        if detail.get("move_path"):
            item["move_path"] = sanitizer.text(detail["move_path"])
        changes.append(item)
    return {
        "call_id": payload.get("call_id"),
        "turn_id": payload.get("turn_id"),
        "success": payload.get("success"),
        "stdout": sanitizer.text(payload.get("stdout", "")),
        "stderr": sanitizer.text(payload.get("stderr", "")),
        "changes": changes,
    }


def selected_events(
    rows: list[dict[str, Any]],
    meta: dict[str, Any],
    agent: str,
    sanitizer: Sanitizer,
    proof_turn_id: str,
) -> list[dict[str, Any]]:
    session_id = meta.get("id")
    if agent == "/root":
        selected_rows = rows[: main_proof_end(rows, proof_turn_id)]
    else:
        selected_rows = rows[own_agent_start(rows, proof_turn_id) :]

    events: list[dict[str, Any]] = []
    seen_visible_messages: set[tuple[Any, ...]] = set()
    for sequence, row in enumerate(selected_rows):
        row_type = row.get("type")
        payload = row.get("payload", {})
        payload_type = payload.get("type") if isinstance(payload, dict) else None

        if row_type == "event_msg" and payload_type == "user_message" and agent == "/root":
            message = sanitizer.text(payload.get("message", ""))
            key = (row.get("timestamp"), "user", message)
            if key not in seen_visible_messages:
                event = event_base(row, session_id, agent, sequence, "message")
                event.update({"role": "user", "phase": "input", "content": message})
                events.append(event)
                seen_visible_messages.add(key)
            continue

        if row_type == "event_msg" and payload_type == "agent_message":
            message = sanitizer.text(payload.get("message", ""))
            key = (row.get("timestamp"), "assistant", payload.get("phase"), message)
            if key not in seen_visible_messages:
                event = event_base(row, session_id, agent, sequence, "message")
                event.update(
                    {
                        "role": "assistant",
                        "phase": payload.get("phase"),
                        "content": message,
                    }
                )
                events.append(event)
                seen_visible_messages.add(key)
            continue

        if row_type == "response_item" and payload_type in {
            "function_call",
            "custom_tool_call",
        }:
            tool = payload.get("name", payload_type)
            arguments = payload.get("arguments", payload.get("input"))
            event = event_base(row, session_id, agent, sequence, "tool_call")
            event.update(
                {
                    "tool": tool,
                    "namespace": payload.get("namespace"),
                    "call_id": payload.get("call_id", payload.get("id")),
                    "arguments": sanitizer.tool_arguments(tool, arguments),
                }
            )
            events.append(event)
            continue

        if row_type == "response_item" and payload_type in {
            "function_call_output",
            "custom_tool_call_output",
        }:
            event = event_base(row, session_id, agent, sequence, "tool_result")
            event.update(
                {
                    "call_id": payload.get("call_id"),
                    "output": sanitizer.value(payload.get("output")),
                }
            )
            events.append(event)
            continue

        if row_type == "response_item" and payload_type == "agent_message":
            event = event_base(
                row, session_id, agent, sequence, "collaboration_message"
            )
            event.update(
                {
                    "author": payload.get("author"),
                    "recipient": payload.get("recipient"),
                    "content": "<encrypted collaboration payload omitted>",
                }
            )
            events.append(event)
            continue

        if row_type == "event_msg" and payload_type == "patch_apply_end":
            event = event_base(row, session_id, agent, sequence, "file_change")
            event.update(patch_summary(payload, sanitizer))
            events.append(event)
            continue

        if row_type == "event_msg" and payload_type in {
            "task_started",
            "task_complete",
            "turn_aborted",
            "sub_agent_activity",
            "context_compacted",
        }:
            event = event_base(row, session_id, agent, sequence, payload_type)
            details = sanitizer.value(
                {
                    k: v
                    for k, v in payload.items()
                    if k
                    not in {
                        "type",
                        "timestamp",
                        "session_id",
                        "agent",
                        "sequence",
                    }
                }
            )
            if payload_type == "sub_agent_activity" and "kind" in details:
                details["activity"] = details.pop("kind")
            else:
                details.pop("kind", None)
            event.update(details)
            events.append(event)
            continue

    return events


def render_conversation(events: list[dict[str, Any]]) -> str:
    lines = [
        "# Main conversation",
        "",
        "This is the visible main-agent transcript for the completed Theorem 6 proof turn.",
        "Times are UTC.",
        "",
    ]
    for event in events:
        if event["agent"] != "/root" or event["kind"] != "message":
            continue
        role = "User" if event["role"] == "user" else "Codex"
        phase = event.get("phase")
        phase_suffix = (
            f" ({phase})"
            if phase and phase not in {"input", "final", "final_answer"}
            else ""
        )
        lines.extend(
            [
                f"## {event['timestamp']} — {role}{phase_suffix}",
                "",
                event.get("content", "").rstrip(),
                "",
            ]
        )
    return "\n".join(lines).rstrip() + "\n"


def lifecycle_by_agent(
    events: list[dict[str, Any]]
) -> dict[str, list[dict[str, Any]]]:
    result: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for event in events:
        if event["kind"] in {"task_complete", "turn_aborted"}:
            result[event["agent"]].append(event)
    return result


def render_agents(
    sessions: list[dict[str, Any]], events: list[dict[str, Any]]
) -> str:
    lifecycle = lifecycle_by_agent(events)
    lines = [
        "# Delegated agent work",
        "",
        "The collaboration payloads in the underlying rollouts are encrypted. This",
        "report therefore records routing metadata plus each agent's own completion",
        "or abort record, which contains the concrete work product and verification",
        "result.",
        "",
        "| Agent | Nickname | Session | Terminal records |",
        "|---|---|---|---:|",
    ]
    for session in sessions:
        if session["agent"] == "/root":
            continue
        agent = session["agent"]
        lines.append(
            f"| `{agent}` | {session.get('nickname') or '—'} | "
            f"`{session['session_id']}` | {len(lifecycle.get(agent, []))} |"
        )
    lines.append("")

    for session in sessions:
        agent = session["agent"]
        if agent == "/root":
            continue
        nickname = session.get("nickname")
        title = f"## `{agent}`"
        if nickname:
            title += f" — {nickname}"
        lines.extend([title, ""])
        records = lifecycle.get(agent, [])
        if not records:
            lines.extend(["No terminal record was captured.", ""])
            continue
        for index, record in enumerate(records, 1):
            status = "completed" if record["kind"] == "task_complete" else "aborted"
            duration = record.get("duration_ms")
            duration_text = f"{duration / 1000:.3f} s" if duration is not None else "unknown"
            lines.extend(
                [
                    f"### Work record {index}: {status}",
                    "",
                    f"- Turn: `{record.get('turn_id', 'unknown')}`",
                    f"- Duration: {duration_text}",
                    "",
                ]
            )
            if record["kind"] == "task_complete":
                lines.extend(
                    [
                        record.get("last_agent_message", "(no completion message)").rstrip(),
                        "",
                    ]
                )
            else:
                lines.extend(
                    [
                        f"Reason: {record.get('reason', 'unknown')}",
                        "",
                    ]
                )
    return "\n".join(lines).rstrip() + "\n"


def collect_file_changes(events: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    paths: dict[str, dict[str, Any]] = {}
    for event in events:
        if event["kind"] != "file_change":
            continue
        for change in event.get("changes", []):
            path = change["path"]
            entry = paths.setdefault(
                path,
                {"agents": set(), "operations": Counter(), "events": 0},
            )
            entry["agents"].add(event["agent"])
            entry["operations"][change.get("change") or "unknown"] += 1
            entry["events"] += 1
    return paths


def render_tool_activity(events: list[dict[str, Any]]) -> str:
    tool_counts: dict[str, Counter[str]] = defaultdict(Counter)
    result_counts: Counter[str] = Counter()
    for event in events:
        if event["kind"] == "tool_call":
            tool_counts[event["agent"]][event.get("tool") or "unknown"] += 1
        elif event["kind"] == "tool_result":
            result_counts[event["agent"]] += 1

    lines = [
        "# Tool and file activity",
        "",
        "## Tool calls by agent",
        "",
        "| Agent | Calls | Results | Most-used tools |",
        "|---|---:|---:|---|",
    ]
    for agent in sorted(tool_counts, key=lambda value: (value != "/root", value)):
        counts = tool_counts[agent]
        common = ", ".join(f"`{name}` × {count}" for name, count in counts.most_common(8))
        lines.append(
            f"| `{agent}` | {sum(counts.values())} | {result_counts[agent]} | {common} |"
        )

    lines.extend(["", "## Files changed through recorded patches", ""])
    file_changes = collect_file_changes(events)
    if not file_changes:
        lines.append("No patch events were captured.")
    else:
        lines.extend(
            [
                "| Portable path | Agents | Recorded operations |",
                "|---|---|---|",
            ]
        )
        for path in sorted(file_changes):
            entry = file_changes[path]
            agents = ", ".join(f"`{agent}`" for agent in sorted(entry["agents"]))
            operations = ", ".join(
                f"{name} × {count}"
                for name, count in sorted(entry["operations"].items())
            )
            lines.append(f"| `{path}` | {agents} | {operations} |")
    return "\n".join(lines).rstrip() + "\n"


def render_schema() -> str:
    return """# Structured trace schema

`trace.json` is an object with these top-level fields:

- `schema_version`: exporter schema version.
- `scope`: thread, proof-turn, and snapshot description.
- `privacy`: transformations applied to the source rollouts.
- `sessions`: safe identity and provenance metadata.
- `events`: the chronological event array.

`trace.jsonl` contains one `export_metadata` object followed by the same events,
one JSON object per line.

Every event has `timestamp`, `session_id`, `agent`, `sequence`, and `kind`.
Additional fields depend on `kind`:

| Kind | Additional fields |
|---|---|
| `message` | `role`, `phase`, `content` |
| `tool_call` | `tool`, `namespace`, `call_id`, `arguments` |
| `tool_result` | `call_id`, `output` |
| `file_change` | `call_id`, `success`, `stdout`, `stderr`, `changes` |
| `task_started` | task timing and turn metadata |
| `task_complete` | task timing and `last_agent_message` |
| `turn_aborted` | task timing and abort `reason` |
| `sub_agent_activity` | delegated agent identity and state |
| `collaboration_message` | `author`, `recipient`, redaction marker |
| `context_compacted` | compaction metadata |

`${WORKSPACE}` and `${HOME}` are portable placeholders for local absolute paths.
"""


def source_manifest(
    discovered: Iterable[
        tuple[Path, list[dict[str, Any]], dict[str, Any], str, str | None]
    ],
) -> list[dict[str, Any]]:
    result = []
    for path, rows, meta, agent, nickname in discovered:
        result.append(
            {
                "agent": agent,
                "nickname": nickname,
                "session_id": meta.get("id"),
                "source_basename": path.name,
                "source_bytes": path.stat().st_size,
                "source_sha256": sha256_file(path),
                "source_records": len(rows),
            }
        )
    return result


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=False) + "\n",
        encoding="utf-8",
    )


def make_archive(output_dir: Path, archive_path: Path) -> None:
    with zipfile.ZipFile(
        archive_path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9
    ) as archive:
        for path in sorted(output_dir.iterdir()):
            if path.is_file():
                archive.write(path, arcname=f"{output_dir.name}/{path.name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--session-dir", type=Path, default=DEFAULT_SESSION_DIR)
    parser.add_argument("--thread-id", default=THREAD_ID)
    parser.add_argument("--proof-turn-id", default=PROOF_TURN_ID)
    parser.add_argument(
        "--workspace",
        type=Path,
        default=Path(__file__).resolve().parents[2],
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
    )
    args = parser.parse_args()

    output_dir = args.output_dir.resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    sanitizer = Sanitizer(args.workspace)
    discovered = discover_sessions(args.session_dir, args.thread_id)

    sessions = []
    events: list[dict[str, Any]] = []
    for path, rows, meta, agent, nickname in discovered:
        sessions.append(
            {
                "agent": agent,
                "nickname": nickname,
                "session_id": meta.get("id"),
                "parent_thread_id": meta.get("parent_thread_id"),
                "source_basename": path.name,
                "started_at": meta.get("timestamp"),
            }
        )
        events.extend(
            selected_events(
                rows,
                meta,
                agent,
                sanitizer,
                args.proof_turn_id,
            )
        )

    events.sort(
        key=lambda event: (
            event.get("timestamp") or "",
            event.get("agent") or "",
            event.get("sequence") or 0,
        )
    )
    sources = source_manifest(discovered)
    generated_at = datetime.now(timezone.utc).isoformat()

    main_completion = next(
        event
        for event in events
        if event["agent"] == "/root"
        and event["kind"] == "task_complete"
        and event.get("turn_id") == args.proof_turn_id
    )
    privacy = {
        "excluded": [
            "model reasoning records",
            "system and developer prompts",
            "environment and world-state snapshots",
            "token accounting",
            "tool schema discovery payloads",
        ],
        "redacted": [
            "encrypted collaboration message payloads",
            "absolute home and workspace paths",
        ],
        "path_placeholders": {
            "${WORKSPACE}": "the repository root",
            "${HOME}": "the exporting user's home directory",
        },
    }
    scope = {
        "thread_id": args.thread_id,
        "proof_turn_id": args.proof_turn_id,
        "description": "Completed Theorem 6 proof turn and all direct sub-agent sessions",
        "cutoff": main_completion.get("timestamp"),
        "excludes_current_export_turn": True,
    }
    trace = {
        "schema_version": SCHEMA_VERSION,
        "generated_at": generated_at,
        "scope": scope,
        "privacy": privacy,
        "sessions": sessions,
        "events": events,
    }

    write_json(output_dir / "trace.json", trace)
    with (output_dir / "trace.jsonl").open("w", encoding="utf-8") as handle:
        handle.write(
            json.dumps(
                {
                    "kind": "export_metadata",
                    "schema_version": SCHEMA_VERSION,
                    "generated_at": generated_at,
                    "scope": scope,
                    "privacy": privacy,
                    "sessions": sessions,
                },
                ensure_ascii=False,
            )
            + "\n"
        )
        for event in events:
            handle.write(json.dumps(event, ensure_ascii=False) + "\n")

    (output_dir / "conversation.md").write_text(
        render_conversation(events), encoding="utf-8"
    )
    (output_dir / "agents.md").write_text(
        render_agents(sessions, events), encoding="utf-8"
    )
    (output_dir / "tool-activity.md").write_text(
        render_tool_activity(events), encoding="utf-8"
    )
    (output_dir / "SCHEMA.md").write_text(render_schema(), encoding="utf-8")
    write_json(output_dir / "source-sessions.json", sources)

    outcome = main_completion.get("last_agent_message", "").rstrip()
    readme = f"""# Theorem 6 agent-trace export

This is a portable snapshot of the completed Codex task that formalized
Theorem 6 of the paper in Lean. It covers the main proof turn and the eight
directly delegated agents.

## Outcome

{outcome}

## Contents

- `conversation.md` — readable main-agent conversation.
- `agents.md` — delegated-agent lifecycle and completion reports.
- `tool-activity.md` — tool counts and patch-touched files.
- `trace.json` — complete selected event trace as structured JSON.
- `trace.jsonl` — the same trace in streaming JSON Lines format.
- `SCHEMA.md` — field and event-kind reference.
- `source-sessions.json` — source rollout IDs, sizes, and SHA-256 provenance.
- `manifest.json` and `SHA256SUMS` — integrity metadata.
- `export_trace.py` — reproducible sanitizer/exporter.

## Privacy and scope

The export intentionally omits model reasoning records and internal
system/developer prompts. Encrypted collaboration payloads remain unavailable
and are represented by an explicit omission marker. Tool calls, tool results,
visible messages, task status, agent completion reports, and patch summaries
are retained. Local paths use `${{WORKSPACE}}` and `${{HOME}}`.

The snapshot ends at `{scope['cutoff']}`, when proof turn
`{args.proof_turn_id}` completed. The later request that created this export is
not recursively included.
"""
    (output_dir / "README.md").write_text(readme, encoding="utf-8")

    manifest_files = []
    for path in sorted(output_dir.iterdir()):
        if path.is_file() and path.name not in {"manifest.json", "SHA256SUMS"}:
            manifest_files.append(
                {
                    "path": path.name,
                    "bytes": path.stat().st_size,
                    "sha256": sha256_file(path),
                }
            )
    manifest = {
        "schema_version": SCHEMA_VERSION,
        "generated_at": generated_at,
        "scope": scope,
        "event_count": len(events),
        "session_count": len(sessions),
        "source_rollouts": sources,
        "export_files": manifest_files,
    }
    write_json(output_dir / "manifest.json", manifest)

    checksum_lines = []
    for path in sorted(output_dir.iterdir()):
        if path.is_file() and path.name != "SHA256SUMS":
            checksum_lines.append(f"{sha256_file(path)}  {path.name}")
    (output_dir / "SHA256SUMS").write_text(
        "\n".join(checksum_lines) + "\n", encoding="utf-8"
    )

    archive_path = output_dir.parent / f"{output_dir.name}.zip"
    make_archive(output_dir, archive_path)
    archive_hash = sha256_file(archive_path)
    checksum_path = archive_path.with_suffix(archive_path.suffix + ".sha256")
    checksum_path.write_text(
        f"{archive_hash}  {archive_path.name}\n", encoding="utf-8"
    )

    print(
        json.dumps(
            {
                "output_dir": str(output_dir),
                "archive": str(archive_path),
                "archive_sha256": archive_hash,
                "sessions": len(sessions),
                "events": len(events),
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
