import StrongRoberson.Proof.Operations

/-!
# Simultaneously smoothing an edge-disjoint family of routes

The lift argument produces one route of length one or two for every target
edge.  This file packages the finite bookkeeping needed to split all of the
length-two routes.  The hypotheses mention edge *copies*, not merely their
endpoints, which is essential for multigraphs.
-/

namespace StrongRoberson

universe u

/-- A finite indexed family of pairwise edge-disjoint length-two routes in a
multigraph. -/
structure EdgeDisjointLengthTwoRoutes
    {α β : Type u} (F : Graph α β) (ι : Type u) where
  firstEdge : ι → β
  secondEdge : ι → β
  left : ι → α
  middle : ι → α
  right : ι → α
  first_isLink : ∀ i,
    F.IsLink (firstEdge i) (left i) (middle i)
  second_isLink : ∀ i,
    F.IsLink (secondEdge i) (middle i) (right i)
  edges_ne : ∀ i, firstEdge i ≠ secondEdge i
  pairwise_disjoint : ∀ {i j}, i ≠ j →
    firstEdge i ≠ firstEdge j ∧
    firstEdge i ≠ secondEdge j ∧
    secondEdge i ≠ firstEdge j ∧
    secondEdge i ≠ secondEdge j

namespace EdgeDisjointLengthTwoRoutes

variable {α β ι : Type u} {F : Graph α β}

/-- An edge copy belonging to one route is different from both copies
belonging to a different route. -/
theorem first_ne_of_ne (R : EdgeDisjointLengthTwoRoutes F ι)
    {i j : ι} (hij : i ≠ j) :
    R.firstEdge i ≠ R.firstEdge j ∧
      R.firstEdge i ≠ R.secondEdge j :=
  ⟨(R.pairwise_disjoint hij).1,
    (R.pairwise_disjoint hij).2.1⟩

theorem second_ne_of_ne (R : EdgeDisjointLengthTwoRoutes F ι)
    {i j : ι} (hij : i ≠ j) :
    R.secondEdge i ≠ R.firstEdge j ∧
      R.secondEdge i ≠ R.secondEdge j :=
  ⟨(R.pairwise_disjoint hij).2.2.1,
    (R.pairwise_disjoint hij).2.2.2⟩

/-- Output of splitting every route in a finite edge-disjoint family.

Besides the new direct links, the result records that every original edge not
used by a route retains its original endpoints. -/
structure SplitResult (R : EdgeDisjointLengthTwoRoutes F ι) where
  graph : Graph α β
  isSplitOffMinor : IsSplitOffMinor graph F
  vertexSet_eq : graph.vertexSet = F.vertexSet
  route_isLink : ∀ i,
    graph.IsLink (R.firstEdge i) (R.left i) (R.right i)
  untouched_isLink : ∀ {e x y},
    F.IsLink e x y →
    (∀ i, e ≠ R.firstEdge i ∧ e ≠ R.secondEdge i) →
    graph.IsLink e x y

/-- Split every member of a finite edge-disjoint family. -/
noncomputable def splitAll
    [Finite ι] (R : EdgeDisjointLengthTwoRoutes F ι) :
    R.SplitResult := by
  classical
  letI := Fintype.ofFinite ι
  let good (s : Finset ι) (K : Graph α β) : Prop :=
    IsSplitOffMinor K F ∧
      K.vertexSet = F.vertexSet ∧
      (∀ i ∈ s,
        K.IsLink (R.firstEdge i) (R.left i) (R.right i)) ∧
      (∀ i ∉ s,
        K.IsLink (R.firstEdge i) (R.left i) (R.middle i) ∧
        K.IsLink (R.secondEdge i) (R.middle i) (R.right i)) ∧
      (∀ {e x y},
        F.IsLink e x y →
        (∀ i, e ≠ R.firstEdge i ∧ e ≠ R.secondEdge i) →
        K.IsLink e x y)
  have hbuild : ∀ s : Finset ι, ∃ K : Graph α β, good s K := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨F, IsSplitOffMinor.refl F, rfl, by simp,
          fun i _ ↦ ⟨R.first_isLink i, R.second_isLink i⟩,
          fun h _ ↦ h⟩
    | @insert i s his ih =>
        obtain ⟨K, hminor, hvertices, hdone, htodo, hkeep⟩ := ih
        have hi := htodo i his
        let K' :=
          splitOff K hi.1 hi.2 (R.edges_ne i)
        have hminor' : IsSplitOffMinor K' F :=
          IsSplitOffMinor.trans
            (IsSplitOffMinor.split K hi.1 hi.2 (R.edges_ne i))
            hminor
        have hvertices' : K'.vertexSet = F.vertexSet := by
          rw [vertexSet_splitOff]
          exact hvertices
        refine ⟨K', hminor', hvertices', ?_, ?_, ?_⟩
        · intro j hj
          rw [Finset.mem_insert] at hj
          rcases hj with hji | hjs
          · subst j
            exact isLink_splitOff_new K hi.1 hi.2 (R.edges_ne i)
          · have hji : j ≠ i := by
              intro h
              subst j
              exact his hjs
            have hne := R.first_ne_of_ne hji
            exact (isLink_splitOff K hi.1 hi.2 (R.edges_ne i)).2
              (Or.inr ⟨hne.1, hne.2, hdone j hjs⟩)
        · intro j hj
          have hji : j ≠ i := by
            intro h
            subst j
            exact hj (Finset.mem_insert_self i s)
          have hjs : j ∉ s := by
            intro h
            exact hj (Finset.mem_insert_of_mem h)
          have hjlinks := htodo j hjs
          have hp := R.first_ne_of_ne hji
          have hq := R.second_ne_of_ne hji
          exact
            ⟨(isLink_splitOff K hi.1 hi.2 (R.edges_ne i)).2
                (Or.inr ⟨hp.1, hp.2, hjlinks.1⟩),
              (isLink_splitOff K hi.1 hi.2 (R.edges_ne i)).2
                (Or.inr ⟨hq.1, hq.2, hjlinks.2⟩)⟩
        · intro e x y he hene
          have held := hkeep he hene
          exact (isLink_splitOff K hi.1 hi.2 (R.edges_ne i)).2
            (Or.inr ⟨(hene i).1, (hene i).2, held⟩)
  let K : Graph α β :=
    Classical.choose (hbuild (Finset.univ : Finset ι))
  have hK : good (Finset.univ : Finset ι) K :=
    Classical.choose_spec (hbuild (Finset.univ : Finset ι))
  exact
    { graph := K
      isSplitOffMinor := hK.1
      vertexSet_eq := hK.2.1
      route_isLink := fun i ↦ hK.2.2.1 i (Finset.mem_univ i)
      untouched_isLink := hK.2.2.2.2 }

end EdgeDisjointLengthTwoRoutes

end StrongRoberson
