# Delegated agent work

The collaboration payloads in the underlying rollouts are encrypted. This
report therefore records routing metadata plus each agent's own completion
or abort record, which contains the concrete work product and verification
result.

| Agent | Nickname | Session | Terminal records |
|---|---|---|---:|
| `/root/paper_map` | Ampere | `019fae00-f56b-7ad3-b544-c56de60353a3` | 7 |
| `/root/lean_structure` | Nietzsche | `019fae01-05c1-79e3-b2fa-efea8e8a7369` | 4 |
| `/root/mathlib_search` | Ramanujan | `019fae01-1794-7890-8a8f-d90b12aec985` | 2 |
| `/root/routed_copy` | Epicurus | `019fae38-268a-74b0-86cb-10ec3f517377` | 5 |
| `/root/orbit_succ` | Wegener | `019fae5c-33af-7632-b1c9-145eaeb55e1b` | 1 |
| `/root/forest_avoidance` | Carson | `019fae65-3d9f-75b2-84ea-c65e7c776ef1` | 1 |
| `/root/chord_ends_orbit` | Boole | `019fae67-76c3-7bf0-af15-e30a1b373301` | 1 |
| `/root/statement_audit` | Leibniz | `019fae72-0cb5-7023-ba9b-eb0074f760e1` | 1 |

## `/root/paper_map` — Ampere

### Work record 1: completed

- Turn: `019fae00-f5d1-7540-ba6b-77c1cff4fdfe`
- Duration: 788.693 s

Read-only proof map completed and sent to the parent agent. No files were changed.

The principal required Lean deviations are:

- Replace the paper’s informal fixed-point iteration with well-founded induction on `|V| + |E|`.
- Contract spanning forests of fiber components, then delete residual internal loops; “contract all internal edges” is not literally valid.
- Track target-edge provenance explicitly after splitting, since the intermediate `F'' → G` is not a homomorphism.
- Allow chord paths of length one or two; the paper incorrectly asserts they are always length two.
- Retain odd isolated vertices or separately formalize component restriction and recombination.
- Add local edge-typed multigraph trail/circuit infrastructure, since Mathlib’s current `Graph` API has no `Graph.Walk`.
- Handle empty targets and disconnected graphs with isolated components, which the paper silently omits.

I also supplied a file-and-lemma dependency order covering finite incidence facts, fiber normalization, component collapse, the lift lemma, progress, and the final induction.

### Work record 2: completed

- Turn: `019fae1b-63c2-72a1-b32b-2cbf34c91698`
- Duration: 2162.867 s

Implemented [FiberReduction.lean](${WORKSPACE}/StrongRoberson/Proof/FiberReduction.lean).

It now includes:

- Fused weight and raw-fibre transport lemmas.
- `smoothAndCollapseState`, preserving fibre sums and degree parity.
- A violating-pair chooser for any non-reduced state.
- Well-founded normalization on `F.edgeSet.ncard`.
- Exported `FiberReductionResult` containing:
  - `graph`
  - `state`
  - `isSplitOffMinor`
  - `reduced`
  - `degree_le_one`

The entry point is `WeightedParityState.normalizeFiberDegrees F S`.

Verification:

- `lake build StrongRoberson.Proof.FiberReduction` succeeds.
- LSP diagnostics are clean.
- Source scans found no `sorry`, `admit`, or added axioms.
- `lean_verify` passed for both `smoothAndCollapseState` and `normalizeFiberDegrees`; only standard classical/quotient axioms are used.

### Work record 3: completed

- Turn: `019fae3c-aef4-7202-8b02-5cafc622266d`
- Duration: 150.506 s

Completed [Reduction.lean](${WORKSPACE}/StrongRoberson/Proof/Reduction.lean).

- Preserved `PerfectFiberReduction` and the exact public theorem signature.
- Removed all dummy `True` lemmas and sorries.
- Assembled normalization, terminal pruning, perfect-fibre proof, and minor-certificate composition.
- Added a necessary empty-target branch.
- LSP diagnostics are clean.
- `lake build StrongRoberson.Proof.Reduction` succeeds.
- `lean_verify` reports no source warnings or nonstandard axioms.

### Work record 4: completed

- Turn: `019fae3f-8c5d-7681-aa6c-3a661e941440`
- Duration: 938.705 s

Created [CoveringOrbit.lean](${WORKSPACE}/StrongRoberson/Proof/CoveringOrbit.lean).

It exports:

- `Fiber`
- `pathTransport`
- `pathTransport_reverse_apply`
- `pathTransportEquiv`
- `pathPermutation`
- Minimal positive return-time, no-earlier-return, and pre-return orbit-injectivity lemmas
- `pathPermutation_exists_minimal_positive_return`

The module builds cleanly, has no sorries, and passes `lean_verify` using only standard classical/quotient axioms.

### Work record 5: completed

- Turn: `019fae4e-a3cb-7e90-a28a-1c45db330778`
- Duration: 277.612 s

Created [OutsidePath.lean](${WORKSPACE}/StrongRoberson/Proof/OutsidePath.lean).

It provides reversal and composition equivalences for `SourcePath.Avoids`, one-edge and nil constructors, component projections, and forward/reverse outside-connectivity wrappers. The module builds cleanly, has no sorries, and passes LSP and axiom verification.

### Work record 6: completed

- Turn: `019fae53-a774-7b60-9cc2-f074ec56d099`
- Duration: 427.585 s

Added [LoopSplice.lean](${WORKSPACE}/StrongRoberson/Proof/LoopSplice.lean) with:

- `Quiver.Path.repeat_succ_left`
- `Quiver.Path.repeat_add_two`
- `transportedPath_repeat_succ_left`
- `transportedPath_repeat_add_two`

The final lemma explicitly isolates the first and last lifted copies around the middle `n` repetitions.

Validation passed:

- Clean Lean LSP diagnostics
- Module build succeeds
- Signature/axiom verification succeeds with only standard axioms
- No `sorry`, `admit`, custom `axiom`, or `unsafe`
- No edits to `LiftForest.lean` or `Lift.lean`

### Work record 7: completed

- Turn: `019fae5c-c6d7-7211-b15a-327e1fb9b473`
- Duration: 536.978 s

Completed both assigned changes:

- Generalized all nine `CoveringConcat`/`CoveringRepeat` covering declarations to independent universes.
- Added [CoveringOneArrow.lean](${WORKSPACE}/StrongRoberson/Proof/CoveringOneArrow.lean) with canonical `liftStar`, endpoint equality, and lifted-path `HEq`.

All affected modules build, LSP diagnostics are clean, and every touched declaration passes source/signature verification. No downstream changes or `LiftForest` edits were needed.

## `/root/lean_structure` — Nietzsche

### Work record 1: completed

- Turn: `019fae01-0615-7353-bb48-2951bb14286a`
- Duration: 1109.205 s

Read-only audit complete; no files were modified.

The existing project compiles cleanly except for the single `sorry` in [MainTheorem.lean](${WORKSPACE}/StrongRoberson/MainTheorem.lean:26).

Exact target:

```lean
∀ {α γ : Type u} [Finite α] [Finite γ]
  (F : SimpleGraph α) (G : SimpleGraph γ)
  (φ : Oddomorphism (simpleToMultiGraph F) G),
  IsSplitOffMinor (simpleToMultiGraph G) (simpleToMultiGraph F)
```

Its current Lean expression hash is `1595059117`. `lean_verify` currently reports `sorryAx`; the final proof should retain the same hash and remove `sorryAx`.

Existing infrastructure is limited to:

- Simple-to-multigraph conversion, homomorphisms, and graph isomorphisms in `Basic.lean`.
- The oddomorphism structure, edge-fibre degree, and one parity lemma in `Oddomorphism.lean`.
- Primitive reattachment, one-edge contraction, one split, and the inductive split-off-minor relation in `SplitOff.lean`.

Mathlib’s edge-typed `Graph` API only supplies incidence, loops, adjacency, maps, deletion, and subgraphs. It has no multigraph walks, paths, circuits, degrees, connectivity, components, forests, or matchings. Those are the main missing foundations. Mathlib’s `SimpleGraph` API does have spanning forests, unique tree paths, cycles, and matching results, so converting simple terminal graphs and using an incidence/subdivision simple graph should save substantial work.

Recommended module DAG:

1. `StrongRoberson/Proof/SplitOffClosure.lean`

   Add `isLink_reattachEdge`, `isLink_splitOff`, `isLink_contractEdge`, the exact contraction vertex-set formula, split/contract cardinality drops, and split-off-minor lemmas for edge/vertex deletion.

2. `StrongRoberson/Proof/MultigraphBasics.lean`

   Define a loop-correct degree or maintain an explicit loopless invariant; prove homomorphic sources are loopless. Add underlying/simple-shadow and incidence-subdivision graph constructions.

3. `StrongRoberson/Proof/EdgeFibers.lean`

   Define the unique target-edge colour of a live source edge, prove fibres partition the edge set, relate fibre degree to `edgeFiberDegree`, and derive surjectivity from `odd_fiber`.

4. `StrongRoberson/Proof/FiberReduction.lean`

   Formalize paper lines 348–366: delete circuit edges, split pairs until every coloured fibre has maximum degree one, prove parity preservation, then characterize retained vertices.

5. `StrongRoberson/Proof/ContractionStep.lean`

   Contract same-target-fibre edges, explicitly delete residual loops, prove the component/boundary parity claim, construct the next oddomorphism, and prove: either the result is a fibrewise lift or its live vertex count is strictly smaller.

6. `StrongRoberson/Proof/Immersion.lean`

   Give a reusable edge-disjoint-path witness and prove such a witness yields `IsSplitOffMinor`.

7. `StrongRoberson/Proof/Lift.lean`

   Define the terminal “fibrewise lift” condition and formalize Lemma 315: choose a full spanning forest, lift one copy, prove the fundamental-cycle path claim, contract outside the chosen copy, and build the immersion. This is likely the hardest isolated lemma.

8. `StrongRoberson/Proof/Termination.lean`

   Replace the informal repetition with strong induction on `H.vertexSet.ncard`, composing split-off-minor witnesses.

9. `MainTheorem.lean`

   Reduce the given oddomorphism to a terminal lift, apply the lift lemma, and compose the two witnesses.

Suggested central statements:

```lean
theorem Oddomorphism.reductionStep :
  ∃ H ψ, IsSplitOffMinor H F ∧
    (FiberwiseLift ψ ∨ H.vertexSet.ncard < F.vertexSet.ncard)

theorem Oddomorphism.exists_fiberwiseLift :
  ∃ H ψ, IsSplitOffMinor H F ∧ FiberwiseLift ψ

theorem FiberwiseLift.target_isSplitOffMinor :
  IsSplitOffMinor (simpleToMultiGraph G) H
```

Required deviations or clarifications from the prose proof:

- The formal theorem permits disconnected targets and isolated target vertices, whereas the paper assumes the connected, nontrivial case. Isolated fibres need explicit representative selection.
- `F''` is not homomorphic to `G`: splitting paths creates edges internal to a target fibre. A fixed target-edge colour must therefore be carried on edge identities through splits.
- `contractEdge` intentionally retains loops. Contracting parallel internal edges creates residual loops, which must be deleted before rebuilding the next homomorphism.
- Paper line 383 is ambiguous about whether contraction starts from `F` or `F''`; formally it must start from the reduced graph.
- For disconnected `G`, the terminal object is naturally a componentwise/fibrewise lift; a single global lift multiplicity need not exist.
- Use well-founded induction on live vertex count instead of “repeat until equality”.
- A faithful Lean-friendly simplification is to delete circuits sequentially and split length-two pairs sequentially, rather than choosing a maximal circuit family and maximal-length paths. Both use exactly the paper’s operations and preserve its invariant.
- Never count loops using only `incidenceSet.ncard`; loops contribute twice to ordinary degree. Maintaining looplessness and deleting newly created loops immediately is simpler.

The lift lemma and the contraction-boundary parity lemma are the two genuinely hard blocks. The primitive operation facts, fibre partition, looplessness, surjectivity, parity conversions, and termination bookkeeping are suitable first proofs after installing the sorry outline.

### Work record 2: completed

- Turn: `019fae1b-3cba-72a1-9e62-eeca5040d9af`
- Duration: 549.985 s

Implemented [Operations.lean](${WORKSPACE}/StrongRoberson/Proof/Operations.lean).

Added:

- Exact `[simp]` `IsLink` lemmas for reattachment, splitting, and contraction.
- Exact contraction vertex map and vertex-set formula.
- Edge/vertex cardinality equations and strict finite decreases.
- `smoothAndCollapse`, which splits a length-two trail, then contracts the new edge or deletes it when it is a loop.
- Edge/vertex formulas and an `IsSplitOffMinor` certificate for the compound operation.
- No `sorry` or `admit`.

Lean diagnostics are clean, `lean_verify` finds no `sorryAx`, and `lake build StrongRoberson.Proof.Operations` succeeds.

### Work record 3: completed

- Turn: `019fae23-da6f-7c82-8f37-c96ced45a7f6`
- Duration: 372.385 s

Updated [Operations.lean](${WORKSPACE}/StrongRoberson/Proof/Operations.lean) with:

```lean
smoothAndCollapse ... =
  (G.map (contractVertexMap u w)).deleteEdges {e₁, e₂}
```

Also added the corresponding exact `[simp]` `IsLink` characterization and lemmas for contraction-map images, singleton preimages, and live-vertex preservation.

No sorries, diagnostics are clean, and the Operations target builds successfully.

### Work record 4: completed

- Turn: `019fae2a-2297-7603-8bff-151bdf5db7af`
- Duration: 850.574 s

Implemented and verified:

- [SubgraphCopy.lean](${WORKSPACE}/StrongRoberson/Proof/SubgraphCopy.lean)
  - Heterogeneous vertex/edge embeddings
  - Exact `IsLink` preservation
  - Parallel-edge identity preservation
  - Image subgraph, `GraphIso`, and `IsSplitOffMinor`

- [CollapseOutside.lean](${WORKSPACE}/StrongRoberson/Proof/CollapseOutside.lean)
  - Finite edge-count contraction recursion
  - Explicit representative trace
  - Protected vertices fixed and distinct
  - Boundary edge copies survive
  - Outside-connected vertices share a representative
  - Terminal graph and `IsSplitOffMinor` certificate

Both targeted builds pass. LSP diagnostics and source scans are clean with no `sorryAx`.

## `/root/mathlib_search` — Ramanujan

### Work record 1: completed

- Turn: `019fae01-17f2-7f70-9f62-1d2396197cb0`
- Duration: 2404.004 s

Implemented [Covering.lean](${WORKSPACE}/StrongRoberson/Proof/Covering.lean) with:

- Edge-copy-preserving source quiver and adjacency target quiver.
- Involutive reversals and induced `MultigraphHom` prefunctor.
- Full proof that perfect fibres give bijective stars and a quiver covering.
- Bijective path stars, path-lift equivalence, explicit lifts, uniqueness, endpoint/map lemmas.
- Simple-graph walk to target-quiver path conversion.
- No `sorry`, `admit`, or custom axioms.

The unchanged `HasPerfectFibers` definition was relocated there, and [Lift.lean](${WORKSPACE}/StrongRoberson/Proof/Lift.lean) now imports it.

Validation:

- Full `lake build` succeeds.
- Covering module has zero diagnostics.
- Axiom verification reports only standard Mathlib axioms: `propext`, `Classical.choice`, and `Quot.sound`.

### Work record 2: completed

- Turn: `019fae26-1fb6-7bc0-83e3-51668370b87d`
- Duration: 5210.168 s

Completed the hard lift/chord case autonomously.

Key result: `MultigraphHom.Covering.chordBoundaryCertificate` now supplies the exact certificate expected by `LiftAssembly`, and `Lift.lean` is wired to it.

Validation passed:

- `lake build StrongRoberson.Proof.Lift`
- Full theorem verification with only standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- No `sorry`, `admit`, `axiom`, or `unsafe` anywhere under `StrongRoberson`
- Signature hash verified: `1595059117`

One paper-proof deviation: the alternate fundamental-cycle arc is represented recursively by outside bridges and intermediate chord edges, rather than as one monolithic repeated lifted path. This is mathematically equivalent and avoids dependent endpoint-cast complexity in Lean.

## `/root/routed_copy` — Epicurus

### Work record 1: completed

- Turn: `019fae38-26f5-77b2-b30e-34c9a8a02652`
- Duration: 502.836 s

Created [RoutedCopy.lean](${WORKSPACE}/StrongRoberson/Proof/RoutedCopy.lean).

It provides edge-identity-safe short routes, simultaneous splitting, an exact `SubgraphCopy`, and:

```lean
StrongRoberson.RoutedCopy.isSplitOffMinor
```

Verification passed with no diagnostics or placeholders. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

### Work record 2: completed

- Turn: `019fae40-453d-71e2-a288-2b9ebec9e055`
- Duration: 687.632 s

Created [LiftAssembly.lean](${WORKSPACE}/StrongRoberson/Proof/LiftAssembly.lean).

Exported conditional theorems:

- `MultigraphHom.Covering.isSplitOffMinor_of_chordBoundaryProvider`
- `MultigraphHom.Covering.perfectFibers_implies_splitOffMinor_of_chordBoundaryProvider`

The exact provider hypothesis is:

```lean
∀ (c : G.ConnectedComponent) (x y : c.supp),
  G.Adj x.1 y.1 →
  ¬ T.graph.Adj x.1 y.1 →
  ChordBoundaryCertificate φ hφ T c x y
```

Diagnostics and targeted build pass. Both theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`.

### Work record 3: completed

- Turn: `019fae4c-2e47-73e2-b856-160a0a269c11`
- Duration: 300.853 s

Created [CoveringConcat.lean](${WORKSPACE}/StrongRoberson/Proof/CoveringConcat.lean).

Exported:

- `pathTransport_comp`
- `transportedPath`
- `transportedPath_comp`
- supporting `liftPath_comp`

Targeted build and diagnostics pass. Both requested lemmas have only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

### Work record 4: completed

- Turn: `019fae52-2170-72b0-87aa-b91cffaca8b2`
- Duration: 223.910 s

Created [CoveringRepeat.lean](${WORKSPACE}/StrongRoberson/Proof/CoveringRepeat.lean).

Key exports:

- `Quiver.Path.repeatClosed`
- `[simp] pathTransport_repeat`
- `transportedPath_repeat_succ`
- `[simp] pathTransport_nil`

Diagnostics and targeted build pass. Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

### Work record 5: completed

- Turn: `019fae58-09b8-7b33-85b1-40f86476f5a2`
- Duration: 929.355 s

Completed and validated:

- [CoveringReverse.lean](${WORKSPACE}/StrongRoberson/Proof/CoveringReverse.lean): acyclic `transportedPath_reverse`
- [CoveringReversePath.lean](${WORKSPACE}/StrongRoberson/Proof/CoveringReversePath.lean): HEq and endpoint-cast avoidance helpers
- [LoopSplice.lean](${WORKSPACE}/StrongRoberson/Proof/LoopSplice.lean): generalized to independent universes

All diagnostics and targeted builds pass.

## `/root/orbit_succ` — Wegener

### Work record 1: aborted

- Turn: `019fae5c-3421-7661-9dc3-9aa8c3a2912f`
- Duration: 29.107 s

Reason: interrupted

## `/root/forest_avoidance` — Carson

### Work record 1: completed

- Turn: `019fae65-3e1c-73d0-bfd9-e51c186fa04f`
- Duration: 803.758 s

Created [ForestAvoidance.lean](${WORKSPACE}/StrongRoberson/Proof/ForestAvoidance.lean) without modifying active proof files.

Exports:

- `componentForestPath_avoids_of_root_ne`
- `componentForestPath_reverse_avoids_of_sheetRoot_ne`

Also added supporting endpoint, concatenation, empty-path, and one-arrow lift lemmas.

Verification:

- Targeted Lake build succeeds.
- Lean LSP reports no diagnostics.
- Both exports verify with only `propext`, `Classical.choice`, and `Quot.sound`.
- Source scan reports no warnings or placeholders.

## `/root/chord_ends_orbit` — Boole

### Work record 1: completed

- Turn: `019fae67-7736-7fa0-b997-a99dc803086e`
- Duration: 468.493 s

Completed [ChordEndsOrbit.lean](${WORKSPACE}/StrongRoberson/Proof/ChordEndsOrbit.lean).

It exports canonical one-arrow lift definitions and exact `eX`/`eY` identifications, plus the predecessor-return endpoint and `2 ≤ returnTime` results.

Verification:

- Targeted Lake build passes.
- Lean LSP reports zero diagnostics.
- Source scan finds no `sorry`, `admit`, or `axiom`.
- Verified axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Exact signatures sent to `/root/mathlib_search`.

## `/root/statement_audit` — Leibniz

### Work record 1: completed

- Turn: `019fae72-0d2a-76b2-ae7f-d0e0d45de51e`
- Duration: 289.479 s

Read-only audit passed at the current state:

- Public theorem statement is unchanged from `git HEAD`; only imports and proof body differ.
- Independent elaboration of both HEAD and current types gives hash `1595059117`.
- No `sorry`, `admit`, custom `axiom`, `unsafe`, `sorryAx`, or `implemented_by` occurs under `StrongRoberson`.
- Relevant LSP diagnostics are clean.
- `lean_verify` reports only `propext`, `Classical.choice`, and `Quot.sound`, with no warnings.
