import StrongRoberson.Proof.Covering
import StrongRoberson.Proof.Operations
import StrongRoberson.Proof.ParityState

/-!
# From a reduced parity state to perfect fibres

Once every coloured fibre degree is at most one, the parity law forces every
weight-one vertex to have degree exactly one towards each adjacent target
fibre.  Every weight-zero vertex is then isolated and can be removed by taking
an induced subgraph.  The remaining homomorphism has perfect fibres.
-/

namespace StrongRoberson

universe u

namespace WeightedParityState

variable
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite α] [Finite β]
    {color : α → γ}

/-- Terminal condition for the fused smoothing reduction. -/
def IsFiberReduced
    (_S : WeightedParityState F G color) : Prop :=
  ∀ (u : α), u ∈ F.vertexSet → ∀ ⦃y : γ⦄,
    G.Adj (color u) y →
      rawColoredFiberDegree F color u y ≤ 1

/-- Any endpoint of a live edge in a reduced state has weight one. -/
theorem weight_eq_one_of_inc
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced)
    {e : β} {u : α} (heu : F.Inc e u) :
    S.weight u = 1 := by
  obtain ⟨v, huv⟩ := heu
  have hadj : G.Adj (color u) (color v) := S.map_isLink huv
  have hemem :
      e ∈ rawColoredFiberEdges F color u (color v) :=
    ⟨huv.edge_mem, v, huv, rfl⟩
  have hpos :
      0 < rawColoredFiberDegree F color u (color v) := by
    apply (Set.ncard_pos
      (s := rawColoredFiberEdges F color u (color v))
      (finite_rawColoredFiberEdges color u (color v))).mpr
    exact ⟨e, hemem⟩
  have hle :=
    hred u huv.left_mem hadj
  have hdegree :
      rawColoredFiberDegree F color u (color v) = 1 := by
    omega
  have hparity :=
    S.degree_parity u huv.left_mem hadj
  simpa only [hdegree, Nat.cast_one] using hparity.symm

/-- Live weight-one ambient vertices. -/
def positiveVertices
    (S : WeightedParityState F G color) : Set α :=
  {u | u ∈ F.vertexSet ∧ S.weight u = 1}

/-- Delete precisely the weight-zero (hence isolated) vertices. -/
def positiveGraph
    (S : WeightedParityState F G color) : Graph α β :=
  F.induce S.positiveVertices

@[simp]
theorem vertexSet_positiveGraph
    (S : WeightedParityState F G color) :
    S.positiveGraph.vertexSet = S.positiveVertices :=
  rfl

/-- In a reduced state, inducing on the weight-one vertices removes no live
edge copy. -/
theorem isLink_positiveGraph_iff
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced)
    {e : β} {u v : α} :
    S.positiveGraph.IsLink e u v ↔ F.IsLink e u v := by
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_, ?_⟩
    · exact ⟨h.left_mem, S.weight_eq_one_of_inc hred h.inc_left⟩
    · exact ⟨h.right_mem, S.weight_eq_one_of_inc hred h.inc_right⟩

@[simp]
theorem edgeSet_positiveGraph
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced) :
    S.positiveGraph.edgeSet = F.edgeSet := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨u, v, huv⟩ :=
      S.positiveGraph.exists_isLink_of_mem_edgeSet he
    exact ((S.isLink_positiveGraph_iff hred).mp huv).edge_mem
  · intro e he
    obtain ⟨u, v, huv⟩ := F.exists_isLink_of_mem_edgeSet he
    exact ((S.isLink_positiveGraph_iff hred).mpr huv).edge_mem

/-- The positive induced graph is a subgraph of the original graph. -/
theorem positiveGraph_le
    (S : WeightedParityState F G color) :
    S.positiveGraph ≤ F :=
  Graph.induce_le fun _ h ↦ h.1

/-- The ambient colouring restricted to the positive graph. -/
def positiveHom
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced) :
    MultigraphHom S.positiveGraph G where
  toFun u := color u.1
  map_isLink := by
    intro e u v h
    exact S.map_isLink ((S.isLink_positiveGraph_iff hred).mp h)

@[simp]
theorem positiveHom_apply
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced)
    (u : S.positiveGraph.vertexSet) :
    S.positiveHom hred u = color u.1 :=
  rfl

/-- The fixed ambient colouring extends `positiveHom`. -/
theorem positiveHom_isAmbientExtension
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced) :
    (S.positiveHom hred).IsAmbientExtension color := by
  intro u hu
  rfl

/-- Passing to the positive graph does not change any ambient coloured fibre
edge set. -/
theorem rawColoredFiberEdges_positiveGraph
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced)
    (u : α) (y : γ) :
    rawColoredFiberEdges S.positiveGraph color u y =
      rawColoredFiberEdges F color u y := by
  ext e
  simp only [rawColoredFiberEdges, Set.mem_setOf_eq,
    S.edgeSet_positiveGraph hred]
  constructor
  · rintro ⟨he, v, huv, hcv⟩
    exact ⟨he, v, (S.isLink_positiveGraph_iff hred).mp huv, hcv⟩
  · rintro ⟨he, v, huv, hcv⟩
    exact ⟨he, v, (S.isLink_positiveGraph_iff hred).mpr huv, hcv⟩

theorem rawColoredFiberDegree_positiveGraph
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced)
    (u : α) (y : γ) :
    rawColoredFiberDegree S.positiveGraph color u y =
      rawColoredFiberDegree F color u y := by
  unfold rawColoredFiberDegree
  rw [S.rawColoredFiberEdges_positiveGraph hred u y]

/-- Every target vertex has a positive source representative. -/
theorem positiveHom_surjective
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced) :
    Function.Surjective (S.positiveHom hred) := by
  intro y
  have hcast :
      ((weightedOddFiber F color S.weight y).ncard : ZMod 2) = 1 := by
    rw [← fiberWeightSum_eq_ncard_weightedOddFiber]
    exact S.fiber_weight_sum y
  have hodd :
      Odd (weightedOddFiber F color S.weight y).ncard :=
    ZMod.natCast_eq_one_iff_odd.mp hcast
  have hnonempty :
      (weightedOddFiber F color S.weight y).Nonempty :=
    (Set.ncard_pos
      (s := weightedOddFiber F color S.weight y)
      (finite_weightedOddFiber color S.weight y)).mp hodd.pos
  obtain ⟨u, hu, hcu, hwu⟩ := hnonempty
  exact ⟨⟨u, hu, hwu⟩, hcu⟩

/-- The positive homomorphism has perfect target-edge fibres. -/
theorem positiveHom_hasPerfectFibers
    (S : WeightedParityState F G color) (hred : S.IsFiberReduced) :
    (S.positiveHom hred).HasPerfectFibers := by
  refine ⟨S.positiveHom_surjective hred, ?_⟩
  intro u y huy
  have huweight : S.weight u.1 = 1 := u.2.2
  have hcast :
      (rawColoredFiberDegree F color u.1 y : ZMod 2) = 1 := by
    rw [← huweight]
    exact S.degree_parity u.1 u.2.1 huy
  have hodd :
      Odd (rawColoredFiberDegree F color u.1 y) :=
    ZMod.natCast_eq_one_iff_odd.mp hcast
  have hle :
      rawColoredFiberDegree F color u.1 y ≤ 1 :=
    hred u.1 u.2.1 huy
  have hdegree :
      rawColoredFiberDegree F color u.1 y = 1 := by
    have hpos := hodd.pos
    omega
  rw [(S.positiveHom hred).edgeFiberDegree_eq_rawColoredFiberDegree
    (S.positiveHom_isAmbientExtension hred) u y]
  rw [S.rawColoredFiberDegree_positiveGraph hred u.1 y, hdegree]

/-- The pruned terminal graph is a split-off minor of the unpruned state. -/
theorem positiveGraph_isSplitOffMinor
    (S : WeightedParityState F G color) :
    IsSplitOffMinor S.positiveGraph F :=
  .subgraph S.positiveGraph_le

end WeightedParityState

end StrongRoberson
