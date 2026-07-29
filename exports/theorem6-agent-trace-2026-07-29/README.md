# Theorem 6 agent-trace export

This is a portable snapshot of the completed Codex task that formalized
Theorem 6 of the paper in Lean. It covers the main proof turn and the eight
directly delegated agents.

## Outcome

Theorem 6 is fully proved with no human intervention required. The public statement remains unchanged in [MainTheorem.lean](${WORKSPACE}/StrongRoberson/MainTheorem.lean:25).

Verification passed:

- Full Lean build: 8,685 jobs.
- No `sorry`, `admit`, custom axioms, or `unsafe`.
- `lean_verify`: only `propext`, `Classical.choice`, and `Quot.sound`.
- Signature hash: `1595059117`, exactly matching the pre-proof hash.
- All auxiliary proof modules also build independently.

The proof follows the paper’s reduction and perfect-lift argument. Formal deviations are documented in [Proof/README.md](${WORKSPACE}/StrongRoberson/Proof/README.md:1), principally:

- Local well-founded smoothing instead of batched maximal circuits/paths.
- Immediate same-fibre contraction after smoothing.
- Explicit handling of disconnected, isolated, and empty targets.
- Only nonloop exterior edges are contracted; residual loops are discarded later.
- A chord route may already have length one.
- The repeated fundamental-cycle arc is assembled recursively from exterior bridges rather than materialized as one dependently typed path.
- Edge provenance and the global protected branch set are recorded explicitly.

Key components are the [fundamental-cycle certificate](${WORKSPACE}/StrongRoberson/Proof/ChordWalk.lean:408), [perfect-fibre lift](${WORKSPACE}/StrongRoberson/Proof/Lift.lean:42), [final composition](${WORKSPACE}/StrongRoberson/Proof/PaperProof.lean:17), and [signature audit](${WORKSPACE}/StrongRoberson/Proof/SignatureAudit.lean:24).

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
are retained. Local paths use `${WORKSPACE}` and `${HOME}`.

The snapshot ends at `2026-07-29T15:22:43.936Z`, when proof turn
`019fae00-2ac1-74e3-ab75-55efd5ce55b1` completed. The later request that created this export is
not recursively included.
