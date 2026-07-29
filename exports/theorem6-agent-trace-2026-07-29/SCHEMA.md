# Structured trace schema

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
