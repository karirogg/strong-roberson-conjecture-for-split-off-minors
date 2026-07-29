import StrongRoberson.Oddomorphism
import StrongRoberson.Proof.Parity

/-!
# Ambient parity states

The reduction in the paper repeatedly changes the live vertex and edge sets of
a multigraph while retaining the ambient vertex and edge types.  Working
directly with `F.vertexSet` at every intermediate stage introduces avoidable
dependent-type bookkeeping.  This file packages the parity data using:

* a fixed colouring of the ambient vertex type;
* weights in `ZMod 2`, supported on the live vertices; and
* degrees counted as sets of ambient edge identities.

No graph operation is defined here.  The results only translate between this
ambient presentation and the existing definition of `Oddomorphism`.
-/

open Set
open scoped BigOperators

namespace StrongRoberson

universe u

/-- The live ambient edge identities incident with `u` whose other endpoint
has colour `y`.

The explicit intersection with `F.edgeSet` is redundant extensionally (an
`IsLink` proof already implies edge membership), but makes finiteness and the
intended ambient-edge interpretation immediate.
-/
def rawColoredFiberEdges
    {α β γ : Type*} (F : Graph α β) (color : α → γ)
    (u : α) (y : γ) : Set β :=
  {e | e ∈ F.edgeSet ∧ ∃ v : α, F.IsLink e u v ∧ color v = y}

/-- Fibre degree computed on the ambient edge type rather than on the live
edge subtype. Parallel edge copies are counted separately. -/
noncomputable def rawColoredFiberDegree
    {α β γ : Type*} (F : Graph α β) (color : α → γ)
    (u : α) (y : γ) : ℕ :=
  (rawColoredFiberEdges F color u y).ncard

theorem finite_rawColoredFiberEdges
    {α β γ : Type*} {F : Graph α β} [Finite F.edgeSet]
    (color : α → γ) (u : α) (y : γ) :
    (rawColoredFiberEdges F color u y).Finite :=
  Set.toFinite F.edgeSet |>.subset fun _ h ↦ h.1

/-- An ambient colouring extends a multigraph homomorphism when it agrees on
all live vertices. -/
def MultigraphHom.IsAmbientExtension
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) (color : α → γ) : Prop :=
  ∀ (u : α) (hu : u ∈ F.vertexSet), color u = φ ⟨u, hu⟩

namespace MultigraphHom

theorem map_isLink_of_isAmbientExtension
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) {color : α → γ}
    (hcolor : φ.IsAmbientExtension color)
    {e : β} {u v : α} (h : F.IsLink e u v) :
    G.Adj (color u) (color v) := by
  rw [hcolor u h.left_mem, hcolor v h.right_mem]
  exact φ.map_isLink h

/-- The subtype-based degree used by `Oddomorphism` agrees with the ambient
edge-identity degree whenever the ambient colouring extends the homomorphism.
-/
theorem rawColoredFiberDegree_eq_edgeFiberDegree
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) {color : α → γ}
    (hcolor : φ.IsAmbientExtension color)
    (u : F.vertexSet) (y : γ) :
    rawColoredFiberDegree F color u.1 y =
      φ.edgeFiberDegree u y := by
  let A : Set F.edgeSet :=
    {e | ∃ v : F.vertexSet,
      F.IsLink e.1 u.1 v.1 ∧ φ v = y}
  have himage :
      rawColoredFiberEdges F color u.1 y =
        ((fun e : F.edgeSet ↦ e.1) '' A) := by
    ext e
    constructor
    · rintro ⟨he, v, huv, hcv⟩
      let ev : F.vertexSet := ⟨v, huv.right_mem⟩
      have hφv : φ ev = y := by
        rw [← hcolor v huv.right_mem]
        exact hcv
      exact ⟨⟨e, he⟩, ⟨ev, huv, hφv⟩, rfl⟩
    · rintro ⟨e', ⟨v, huv, hφv⟩, rfl⟩
      refine ⟨e'.property, v.1, huv, ?_⟩
      rw [hcolor v.1 v.2]
      exact hφv
  rw [rawColoredFiberDegree, himage,
    (Subtype.val_injective.injOn.ncard_image : _)]
  rfl

/-- The same comparison with the equality oriented towards the ambient
degree. -/
theorem edgeFiberDegree_eq_rawColoredFiberDegree
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) {color : α → γ}
    (hcolor : φ.IsAmbientExtension color)
    (u : F.vertexSet) (y : γ) :
    φ.edgeFiberDegree u y =
      rawColoredFiberDegree F color u.1 y :=
  (φ.rawColoredFiberDegree_eq_edgeFiberDegree hcolor u y).symm

end MultigraphHom

/-- The sum of ambient vertex weights in the live fibre over `y`. -/
noncomputable def fiberWeightSum
    {α β γ : Type*} (F : Graph α β) (color : α → γ)
    (weight : α → ZMod 2) (y : γ) [Finite F.vertexSet] : ZMod 2 := by
  classical
  exact ∑ u ∈ (Set.toFinite F.vertexSet).toFinset,
    if color u = y then weight u else 0

/-- A `ZMod 2` value is the indicator of its being equal to one. -/
theorem ZMod.eq_ite_eq_one (a : ZMod 2) :
    a = if a = 1 then 1 else 0 := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;> simp

/-- The live vertices over `y` carrying weight one. -/
def weightedOddFiber
    {α β γ : Type*} (F : Graph α β) (color : α → γ)
    (weight : α → ZMod 2) (y : γ) : Set α :=
  {u | u ∈ F.vertexSet ∧ color u = y ∧ weight u = 1}

theorem finite_weightedOddFiber
    {α β γ : Type*} {F : Graph α β} [Finite F.vertexSet]
    (color : α → γ) (weight : α → ZMod 2) (y : γ) :
    (weightedOddFiber F color weight y).Finite :=
  Set.toFinite F.vertexSet |>.subset fun _ h ↦ h.1

/-- Over `ZMod 2`, a finite sum of weights is the cardinality modulo two of
the vertices whose weight is one. -/
theorem fiberWeightSum_eq_ncard_weightedOddFiber
    {α β γ : Type*} (F : Graph α β) [Finite F.vertexSet]
    (color : α → γ) (weight : α → ZMod 2) (y : γ) :
    fiberWeightSum F color weight y =
      ((weightedOddFiber F color weight y).ncard : ZMod 2) := by
  classical
  unfold fiberWeightSum
  let live : Finset α := (Set.toFinite F.vertexSet).toFinset
  calc
    (∑ u ∈ live, if color u = y then weight u else 0)
        = ∑ u ∈ live,
            if color u = y ∧ weight u = 1 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro u hu
          by_cases hcolor : color u = y
          · simp only [hcolor, true_and, if_true]
            exact ZMod.eq_ite_eq_one (weight u)
          · simp [hcolor]
    _ = (((live.filter fun u ↦
          color u = y ∧ weight u = 1).card : ℕ) : ZMod 2) := by
          simpa only using
            (Finset.sum_boole
              (fun u : α ↦ color u = y ∧ weight u = 1) live)
    _ = ((weightedOddFiber F color weight y).ncard : ZMod 2) := by
          congr 1
          rw [Set.ncard_eq_toFinset_card
            (weightedOddFiber F color weight y)
            (finite_weightedOddFiber color weight y)]
          congr 1
          ext u
          simp only [live, Finset.mem_filter, Set.Finite.mem_toFinset,
            weightedOddFiber, Set.mem_setOf_eq]

/-- A weighted homomorphism/parity state on a fixed ambient vertex colouring.

Weights outside the live vertex set are required to vanish. The two parity
conditions are the `ZMod 2` versions of the two clauses in `Oddomorphism`.
-/
structure WeightedParityState
    {α β γ : Type u} (F : Graph α β) (G : SimpleGraph γ)
    [Finite F.vertexSet] [Finite F.edgeSet]
    (color : α → γ) where
  weight : α → ZMod 2
  weight_eq_zero_of_not_mem :
    ∀ ⦃u : α⦄, u ∉ F.vertexSet → weight u = 0
  map_isLink :
    ∀ ⦃e : β⦄ ⦃u v : α⦄, F.IsLink e u v → G.Adj (color u) (color v)
  fiber_weight_sum :
    ∀ y : γ, fiberWeightSum F color weight y = 1
  degree_parity :
    ∀ (u : α), u ∈ F.vertexSet → ∀ ⦃y : γ⦄,
      G.Adj (color u) y →
        (rawColoredFiberDegree F color u y : ZMod 2) = weight u

namespace Oddomorphism

/-- The odd/even labelling of an oddomorphism as an ambient `ZMod 2` weight.
The value is zero away from the live vertex set. -/
noncomputable def ambientWeight
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) (u : α) : ZMod 2 := by
  classical
  exact if hu : u ∈ F.vertexSet then
    if (⟨u, hu⟩ : F.vertexSet) ∈ φ.oddVertices then 1 else 0
  else 0

@[simp]
theorem ambientWeight_eq_zero_of_not_mem
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) {u : α} (hu : u ∉ F.vertexSet) :
    φ.ambientWeight u = 0 := by
  simp [ambientWeight, hu]

theorem ambientWeight_eq_one_of_mem_odd
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) {u : α} (hu : u ∈ F.vertexSet)
    (hodd : (⟨u, hu⟩ : F.vertexSet) ∈ φ.oddVertices) :
    φ.ambientWeight u = 1 := by
  classical
  simp [ambientWeight, hu, hodd]

theorem ambientWeight_eq_zero_of_not_mem_odd
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) {u : α} (hu : u ∈ F.vertexSet)
    (hodd : (⟨u, hu⟩ : F.vertexSet) ∉ φ.oddVertices) :
    φ.ambientWeight u = 0 := by
  classical
  simp [ambientWeight, hu, hodd]

theorem ambientWeight_eq_one_iff
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) {u : α} (hu : u ∈ F.vertexSet) :
    φ.ambientWeight u = 1 ↔
      (⟨u, hu⟩ : F.vertexSet) ∈ φ.oddVertices := by
  classical
  constructor
  · intro hweight
    by_contra hodd
    rw [φ.ambientWeight_eq_zero_of_not_mem_odd hu hodd] at hweight
    exact zero_ne_one hweight
  · exact φ.ambientWeight_eq_one_of_mem_odd hu

/-- The ambient vertices of weight one over a target vertex are the image of
the corresponding subtype fibre in the original oddomorphism. -/
theorem weightedOddFiber_ambientWeight_eq_image
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) {color : α → γ}
    (hcolor : φ.toMultigraphHom.IsAmbientExtension color)
    (y : γ) :
    weightedOddFiber F color φ.ambientWeight y =
      Subtype.val '' {u : F.vertexSet |
        u ∈ φ.oddVertices ∧ φ u = y} := by
  ext u
  constructor
  · rintro ⟨hu, hcu, hwu⟩
    have hodd :
        (⟨u, hu⟩ : F.vertexSet) ∈ φ.oddVertices :=
      (φ.ambientWeight_eq_one_iff hu).mp hwu
    have hφu : φ ⟨u, hu⟩ = y := by
      rw [← hcolor u hu]
      exact hcu
    exact ⟨⟨u, hu⟩, ⟨hodd, hφu⟩, rfl⟩
  · rintro ⟨u', ⟨hodd, hφu⟩, rfl⟩
    refine ⟨u'.property, ?_, ?_⟩
    · rw [hcolor u'.1 u'.2]
      exact hφu
    · exact (φ.ambientWeight_eq_one_iff u'.2).mpr hodd

theorem ncard_weightedOddFiber_ambientWeight
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) {color : α → γ}
    (hcolor : φ.toMultigraphHom.IsAmbientExtension color)
    (y : γ) :
    (weightedOddFiber F color φ.ambientWeight y).ncard =
      {u : F.vertexSet |
        u ∈ φ.oddVertices ∧ φ u = y}.ncard := by
  rw [φ.weightedOddFiber_ambientWeight_eq_image hcolor y,
    Subtype.val_injective.injOn.ncard_image]

/-- Convert an oddomorphism to its ambient weighted parity state. -/
noncomputable def toWeightedParityState
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) (color : α → γ)
    (hcolor : φ.toMultigraphHom.IsAmbientExtension color) :
    WeightedParityState F G color where
  weight := φ.ambientWeight
  weight_eq_zero_of_not_mem := by
    intro u hu
    exact φ.ambientWeight_eq_zero_of_not_mem hu
  map_isLink := by
    intro e u v h
    exact φ.toMultigraphHom.map_isLink_of_isAmbientExtension hcolor h
  fiber_weight_sum := by
    intro y
    rw [fiberWeightSum_eq_ncard_weightedOddFiber,
      φ.ncard_weightedOddFiber_ambientWeight hcolor y]
    exact ZMod.natCast_eq_one_iff_odd.mpr (φ.odd_fiber y)
  degree_parity := by
    intro u hu y huy
    have huy' : G.Adj (φ ⟨u, hu⟩) y := by
      rwa [← hcolor u hu]
    rw [φ.toMultigraphHom.rawColoredFiberDegree_eq_edgeFiberDegree
      hcolor ⟨u, hu⟩ y]
    by_cases hodd : (⟨u, hu⟩ : F.vertexSet) ∈ φ.oddVertices
    · rw [(φ.ambientWeight_eq_one_iff hu).mpr hodd]
      exact ZMod.natCast_eq_one_iff_odd.mpr
        ((φ.degree_parity ⟨u, hu⟩ huy').mp hodd)
    · rw [φ.ambientWeight_eq_zero_of_not_mem_odd hu hodd]
      exact ZMod.natCast_eq_zero_iff_even.mpr
        ((φ.edgeFiberDegree_even_iff_not_mem_oddVertices
          ⟨u, hu⟩ huy').mpr hodd)

/-- For a source obtained from a simple graph, every ambient vertex is live,
so an oddomorphism itself supplies the canonical ambient colouring. -/
def simpleAmbientColor
    {α γ : Type*} {F : SimpleGraph α} {G : SimpleGraph γ}
    [Finite α]
    (φ : Oddomorphism (simpleToMultiGraph F) G) (u : α) : γ :=
  φ ⟨u, by simp⟩

theorem simpleAmbientColor_isAmbientExtension
    {α γ : Type*} {F : SimpleGraph α} {G : SimpleGraph γ}
    [Finite α]
    (φ : Oddomorphism (simpleToMultiGraph F) G) :
    φ.toMultigraphHom.IsAmbientExtension φ.simpleAmbientColor := by
  intro u hu
  rfl

/-- Canonical weighted state for an oddomorphism whose source is a simple
graph viewed as a multigraph. -/
noncomputable def toWeightedParityStateSimple
    {α γ : Type u} {F : SimpleGraph α} {G : SimpleGraph γ}
    [Finite α]
    (φ : Oddomorphism (simpleToMultiGraph F) G) :
    WeightedParityState (simpleToMultiGraph F) G φ.simpleAmbientColor :=
  φ.toWeightedParityState φ.simpleAmbientColor
    φ.simpleAmbientColor_isAmbientExtension

end Oddomorphism

namespace WeightedParityState

variable
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    {color : α → γ}

/-- The homomorphism on live vertices underlying a weighted parity state. -/
def toMultigraphHom (S : WeightedParityState F G color) :
    MultigraphHom F G where
  toFun u := color u.1
  map_isLink := by
    intro e u v h
    exact S.map_isLink h

@[simp]
theorem toMultigraphHom_apply
    (S : WeightedParityState F G color) (u : F.vertexSet) :
    S.toMultigraphHom u = color u.1 :=
  rfl

/-- The fixed ambient colouring tautologically extends the homomorphism
obtained from a weighted state. -/
theorem toMultigraphHom_isAmbientExtension
    (S : WeightedParityState F G color) :
    S.toMultigraphHom.IsAmbientExtension color := by
  intro u hu
  rfl

/-- The vertices of weight one, expressed on the live vertex subtype. -/
def oddVertices (S : WeightedParityState F G color) : Set F.vertexSet :=
  {u | S.weight u.1 = 1}

/-- The degree law expressed with ordinary oddness rather than a cast into
`ZMod 2`. -/
theorem odd_rawColoredFiberDegree_iff
    (S : WeightedParityState F G color)
    (u : α) (hu : u ∈ F.vertexSet) {y : γ}
    (huy : G.Adj (color u) y) :
    Odd (rawColoredFiberDegree F color u y) ↔ S.weight u = 1 := by
  rw [← ZMod.natCast_eq_one_iff_odd, S.degree_parity u hu huy]

/-- The even counterpart of `odd_rawColoredFiberDegree_iff`. -/
theorem even_rawColoredFiberDegree_iff
    (S : WeightedParityState F G color)
    (u : α) (hu : u ∈ F.vertexSet) {y : γ}
    (huy : G.Adj (color u) y) :
    Even (rawColoredFiberDegree F color u y) ↔ S.weight u = 0 := by
  rw [← ZMod.natCast_eq_zero_iff_even, S.degree_parity u hu huy]

/-- The ambient weight-one fibre is the image of the corresponding live
subtype fibre. -/
theorem weightedOddFiber_eq_image
    (S : WeightedParityState F G color) (y : γ) :
    weightedOddFiber F color S.weight y =
      Subtype.val '' {u : F.vertexSet |
        u ∈ S.oddVertices ∧ S.toMultigraphHom u = y} := by
  ext u
  constructor
  · rintro ⟨hu, hcu, hwu⟩
    exact ⟨⟨u, hu⟩, ⟨hwu, hcu⟩, rfl⟩
  · rintro ⟨u', ⟨hwu, hcu⟩, rfl⟩
    exact ⟨u'.property, hcu, hwu⟩

theorem ncard_weightedOddFiber
    (S : WeightedParityState F G color) (y : γ) :
    (weightedOddFiber F color S.weight y).ncard =
      {u : F.vertexSet |
        u ∈ S.oddVertices ∧ S.toMultigraphHom u = y}.ncard := by
  rw [S.weightedOddFiber_eq_image y,
    Subtype.val_injective.injOn.ncard_image]

/-- Recover an oddomorphism from an ambient weighted parity state. -/
noncomputable def toOddomorphism
    (S : WeightedParityState F G color) :
    Oddomorphism F G where
  toFun u := color u.1
  map_isLink := by
    intro e u v h
    exact S.map_isLink h
  oddVertices := S.oddVertices
  odd_fiber := by
    intro y
    apply ZMod.natCast_eq_one_iff_odd.mp
    change
      (({u : F.vertexSet |
        u ∈ S.oddVertices ∧ S.toMultigraphHom u = y}.ncard : ℕ) :
          ZMod 2) = 1
    rw [← S.ncard_weightedOddFiber y,
      ← fiberWeightSum_eq_ncard_weightedOddFiber]
    exact S.fiber_weight_sum y
  degree_parity := by
    intro u y huy
    change S.weight u.1 = 1 ↔
      Odd (S.toMultigraphHom.edgeFiberDegree u y)
    rw [← ZMod.natCast_eq_one_iff_odd]
    have hdegree :
        (S.toMultigraphHom.edgeFiberDegree u y : ZMod 2) =
          S.weight u.1 := by
      rw [S.toMultigraphHom.edgeFiberDegree_eq_rawColoredFiberDegree
        S.toMultigraphHom_isAmbientExtension u y]
      exact S.degree_parity u.1 u.2 huy
    rw [hdegree]

@[simp]
theorem toOddomorphism_apply
    (S : WeightedParityState F G color) (u : F.vertexSet) :
    S.toOddomorphism u = color u.1 :=
  rfl

@[simp]
theorem oddVertices_toOddomorphism
    (S : WeightedParityState F G color) :
    S.toOddomorphism.oddVertices = S.oddVertices :=
  rfl

/-- Converting a state to an oddomorphism and reading its ambient weight
recovers the original supported weight. -/
theorem ambientWeight_toOddomorphism
    (S : WeightedParityState F G color) (u : α) :
    S.toOddomorphism.ambientWeight u = S.weight u := by
  by_cases hu : u ∈ F.vertexSet
  · classical
    by_cases hw : S.weight u = 1
    · simp [Oddomorphism.ambientWeight, hu, oddVertices, hw]
    · have hz : S.weight u = 0 := by
        rcases zmod_two_eq_zero_or_one (S.weight u) with hz | ho
        · exact hz
        · exact (hw ho).elim
      simp [Oddomorphism.ambientWeight, hu, oddVertices, hz]
  · rw [S.toOddomorphism.ambientWeight_eq_zero_of_not_mem hu]
    exact (S.weight_eq_zero_of_not_mem hu).symm

end WeightedParityState

namespace Oddomorphism

theorem oddVertices_toWeightedParityState
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) (color : α → γ)
    (hcolor : φ.toMultigraphHom.IsAmbientExtension color) :
    (φ.toWeightedParityState color hcolor).oddVertices =
      φ.oddVertices := by
  ext u
  exact φ.ambientWeight_eq_one_iff u.2

theorem toOddomorphism_toWeightedParityState_apply
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) (color : α → γ)
    (hcolor : φ.toMultigraphHom.IsAmbientExtension color)
    (u : F.vertexSet) :
    (φ.toWeightedParityState color hcolor).toOddomorphism u = φ u := by
  exact hcolor u.1 u.2

end Oddomorphism

end StrongRoberson
