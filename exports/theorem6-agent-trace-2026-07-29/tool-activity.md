# Tool and file activity

## Tool calls by agent

| Agent | Calls | Results | Most-used tools |
|---|---:|---:|---|
| `/root` | 460 | 460 | `exec_command` × 174, `send_message` × 59, `lean_diagnostic_messages` × 40, `lean_run_code` × 26, `wait_agent` × 26, `lean_local_search` × 24, `list_agents` × 22, `apply_patch` × 19 |
| `/root/chord_ends_orbit` | 35 | 35 | `exec` × 12, `lean_verify` × 6, `lean_diagnostic_messages` × 5, `send_message` × 4, `apply_patch` × 3, `lean_local_search` × 2, `list_agents` × 1, `wait_agent` × 1 |
| `/root/forest_avoidance` | 52 | 52 | `exec_command` × 20, `lean_diagnostic_messages` × 9, `apply_patch` × 8, `send_message` × 4, `lean_local_search` × 3, `lean_goal` × 2, `lean_hover_info` × 2, `lean_run_code` × 2 |
| `/root/lean_structure` | 150 | 150 | `exec` × 36, `lean_diagnostic_messages` × 21, `lean_run_code` × 21, `apply_patch` × 20, `exec_command` × 19, `update_plan` × 10, `send_message` × 9, `lean_verify` × 6 |
| `/root/mathlib_search` | 453 | 453 | `apply_patch` × 83, `lean_run_code` × 81, `exec_command` × 69, `lean_diagnostic_messages` × 58, `send_message` × 52, `exec` × 44, `lean_leansearch` × 35, `lean_local_search` × 9 |
| `/root/orbit_succ` | 3 | 3 | `exec` × 2, `lean_diagnostic_messages` × 1 |
| `/root/paper_map` | 307 | 307 | `exec` × 87, `lean_run_code` × 60, `lean_diagnostic_messages` × 41, `apply_patch` × 34, `send_message` × 27, `exec_command` × 17, `lean_local_search` × 14, `lean_build` × 6 |
| `/root/routed_copy` | 163 | 163 | `exec` × 50, `lean_diagnostic_messages` × 28, `send_message` × 24, `apply_patch` × 21, `wait_agent` × 14, `lean_verify` × 10, `lean_run_code` × 8, `lean_build` × 5 |
| `/root/statement_audit` | 22 | 22 | `lean_diagnostic_messages` × 7, `lean_run_code` × 5, `exec` × 3, `lean_verify` × 2, `wait_agent` × 2, `exec_command` × 1, `send_message` × 1, `list_agents` × 1 |

## Files changed through recorded patches

| Portable path | Agents | Recorded operations |
|---|---|---|
| `${WORKSPACE}/StrongRoberson/MainTheorem.lean` | `/root` | update × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/ChordEndsOrbit.lean` | `/root/chord_ends_orbit` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/ChordWalk.lean` | `/root/mathlib_search` | add × 1, update × 15 |
| `${WORKSPACE}/StrongRoberson/Proof/CollapseOutside.lean` | `/root/lean_structure` | add × 1, update × 4 |
| `${WORKSPACE}/StrongRoberson/Proof/ConcatScratch.lean` | `/root` | add × 1, delete × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/Covering.lean` | `/root/mathlib_search` | add × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/CoveringConcat.lean` | `/root/paper_map`, `/root/routed_copy` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/CoveringOneArrow.lean` | `/root/paper_map` | add × 1, update × 4 |
| `${WORKSPACE}/StrongRoberson/Proof/CoveringOrbit.lean` | `/root/paper_map` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/CoveringRepeat.lean` | `/root/paper_map`, `/root/routed_copy` | add × 1, update × 4 |
| `${WORKSPACE}/StrongRoberson/Proof/CoveringReverse.lean` | `/root/routed_copy` | add × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/CoveringReversePath.lean` | `/root/routed_copy` | add × 1, update × 3 |
| `${WORKSPACE}/StrongRoberson/Proof/FiberReduction.lean` | `/root/paper_map` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/ForestAvoidance.lean` | `/root/forest_avoidance` | add × 1, update × 7 |
| `${WORKSPACE}/StrongRoberson/Proof/Lift.lean` | `/root`, `/root/mathlib_search` | add × 1, update × 5 |
| `${WORKSPACE}/StrongRoberson/Proof/LiftAssembly.lean` | `/root/routed_copy` | add × 1, update × 6 |
| `${WORKSPACE}/StrongRoberson/Proof/LiftForest.lean` | `/root/mathlib_search` | add × 1, update × 64 |
| `${WORKSPACE}/StrongRoberson/Proof/LoopSplice.lean` | `/root/paper_map`, `/root/routed_copy` | add × 1, update × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/Operations.lean` | `/root`, `/root/lean_structure` | add × 1, update × 12 |
| `${WORKSPACE}/StrongRoberson/Proof/OutsidePath.lean` | `/root/paper_map` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/PaperProof.lean` | `/root` | add × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/Parity.lean` | `/root` | add × 1, update × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/ParityState.lean` | `/root/paper_map` | add × 1, update × 15 |
| `${WORKSPACE}/StrongRoberson/Proof/README.md` | `/root` | add × 1, update × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/Reduction.lean` | `/root`, `/root/paper_map` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/RouteSplitting.lean` | `/root` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/RoutedCopy.lean` | `/root/routed_copy` | add × 1, update × 3 |
| `${WORKSPACE}/StrongRoberson/Proof/SignatureAudit.lean` | `/root` | add × 1 |
| `${WORKSPACE}/StrongRoberson/Proof/SubgraphCopy.lean` | `/root/lean_structure` | add × 1, update × 2 |
| `${WORKSPACE}/StrongRoberson/Proof/Terminal.lean` | `/root` | add × 1, update × 2 |
