# Proof map for Theorem 6

Target (unchanged):

```lean
StrongRoberson.oddomorphism_implies_splitOffMinor
```

The proof-support modules in this directory are only for Theorem 6 of
`paper-source/main.tex`.

## Paper-to-Lean decomposition

1. `Operations.lean` derives compositional facts about the existing
   split-off, contraction, subgraph, and isomorphism definitions.
2. `Parity.lean`, `ParityState.lean`, `Terminal.lean`, and
   `FiberReduction.lean` record the parity invariant behind `F''` and `F₁`
   and iterate the paper's smoothing/contraction move until every target-edge
   fibre is a perfect matching.
3. `Reduction.lean` packages that iteration as a split-off-minor certificate.
4. `Covering.lean`, `CoveringOrbit.lean`, `CoveringConcat.lean`,
   `CoveringRepeat.lean`, `CoveringReverse.lean`, and
   `CoveringOneArrow.lean` supply unique path lifting and finite monodromy.
5. `LiftForest.lean`, `OutsidePath.lean`, and `ForestAvoidance.lean` choose a
   coherent lifted spanning forest and prove that other sheets avoid it.
6. `ChordWalk.lean` formalizes the fundamental-cycle argument for every
   non-forest target edge. `ChordEndsOrbit.lean` records stronger canonical
   first/last edge identities used to audit that construction.
7. `CollapseOutside.lean`, `RouteSplitting.lean`, `SubgraphCopy.lean`,
   `RoutedCopy.lean`, and `LiftAssembly.lean` contract the exterior, split the
   resulting edge-disjoint short routes, and extract a target copy.
8. `Lift.lean` proves paper Lemma `perfect-matching-lm`;
   `PaperProof.lean` composes it with the reduction certificate.

## Explicit formal deviations and repairs

- The paper chooses maximal families of circuits and maximal paths, then
  informally repeats until a fixed point.  Lean uses local length-two
  smoothing moves and well-founded induction on a finite live-edge measure.
- A local smoothing is immediately followed by the same-fibre contraction
  which the paper postpones.  This is the same pair of allowed operations,
  but it keeps every recursive state homomorphic to `G`.
- The formal theorem permits disconnected targets, isolated target vertices,
  and empty types.  The proof works componentwise through a spanning forest
  and explicitly retains one representative above an isolated target vertex.
- Contracting "all" edges in a fibre can create loops.  Formal contraction
  uses a spanning forest (or an equivalent terminating sequence) and deletes
  residual loops.
- In the lift lemma, a non-tree target edge can already lift directly between
  the selected branch vertices.  Its route therefore has length one *or*
  reduces to length two, not always length two as the prose says.
- The paper describes the other arc of one lifted fundamental cycle as a
  single repeated path.  `ChordWalk.lean` assembles the same arc recursively
  from outside bridges `Y_k → X_{k+1}` and the intervening chord edges.  This
  retains the same least-return orbit and the same first/last chord copies,
  while avoiding dependent endpoint casts for one monolithic path.
- Intermediate split graphs need target-edge provenance because they need not
  map homomorphically to `G`.  The fused local move avoids exposing such a
  graph as a recursive state; where an intermediate is used, the retained
  edge identity supplies the provenance.

## Audit

Before proof development, Lean's expression hash of the exact theorem type
was:

```text
1595059117
```

The completed audit reproduces that value.  The project and all proof modules
build, the source scan contains no placeholders or custom axioms, and
`lean_verify` reports only `propext`, `Classical.choice`, and `Quot.sound`.
