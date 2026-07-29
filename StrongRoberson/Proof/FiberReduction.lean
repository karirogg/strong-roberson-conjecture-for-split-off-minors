import StrongRoberson.Proof.Operations
import StrongRoberson.Proof.ParityState
import StrongRoberson.Proof.Terminal

/-!
# Fibre-degree reduction by fused smoothing

This file formalizes the local move used in the parity reduction.  Given a
length-two trail

`u -[e₁]- v -[e₂]- w`

whose outer endpoints have the same target colour, we smooth the two edge
copies and immediately collapse the resulting monochromatic edge.  The two
operations are fused because their combination has a particularly simple
normal form: identify `w` with `u` and delete `e₁,e₂`.

The local construction is then iterated using the number of live edge copies
as a well-founded measure.
-/

open Set
open scoped BigOperators

namespace StrongRoberson

universe u

/-! ## Raw fibre-edge transport -/

/-- Membership of a fixed edge in a raw coloured fibre, expressed using any
known pair of endpoints of that edge. -/
theorem mem_rawColoredFiberEdges_iff_of_isLink
    {α β γ : Type*} {F : Graph α β} {color : α → γ}
    {e : β} {a b x : α} {y : γ} (h : F.IsLink e a b) :
    e ∈ rawColoredFiberEdges F color x y ↔
      (x = a ∧ color b = y) ∨ (x = b ∧ color a = y) := by
  constructor
  · rintro ⟨_, z, hxz, hcz⟩
    rcases h.eq_and_eq_or_eq_and_eq hxz with hsame | hswap
    · exact Or.inl ⟨hsame.1.symm, hsame.2 ▸ hcz⟩
    · exact Or.inr ⟨hswap.2.symm, hswap.1 ▸ hcz⟩
  · rintro (⟨rfl, hcy⟩ | ⟨rfl, hcy⟩)
    · exact ⟨h.edge_mem, b, h, hcy⟩
    · exact ⟨h.edge_mem, a, h.symm, hcy⟩

/-- Identifying two vertices of the same target colour does not change the
colour of any ambient vertex. -/
theorem color_contractVertexMap
    {α γ : Type*} {color : α → γ} {u w : α}
    (hc : color u = color w) (x : α) :
    color (contractVertexMap u w x) = color x := by
  by_cases hx : x = w
  · subst x
    simpa using hc
  · simp [contractVertexMap_of_ne hx]

/-- Pointwise raw-fibre membership after fused smoothing.  This is the
edge-identity form of `smoothAndCollapse_eq_map_deleteEdges`. -/
theorem mem_rawColoredFiberEdges_smoothAndCollapse_iff
    {α β γ : Type*} {F : Graph α β} {color : α → γ}
    {e₁ e₂ f : β} {u v w x : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w) :
    f ∈ rawColoredFiberEdges
        (smoothAndCollapse F h₁ h₂ hne) color x y ↔
      f ≠ e₁ ∧ f ≠ e₂ ∧
        ∃ x' z', F.IsLink f x' z' ∧
          contractVertexMap u w x' = x ∧ color z' = y := by
  constructor
  · rintro ⟨_, z, hxz, hcz⟩
    rw [isLink_smoothAndCollapse] at hxz
    rcases hxz with
      ⟨hf₁, hf₂, x', z', hx'z', hx', hz'⟩
    refine ⟨hf₁, hf₂, x', z', hx'z', hx', ?_⟩
    rw [← color_contractVertexMap hc z', hz']
    exact hcz
  · rintro ⟨hf₁, hf₂, x', z', hx'z', hx', hcz'⟩
    have hlink :=
      (isLink_smoothAndCollapse F h₁ h₂ hne).2
        ⟨hf₁, hf₂, x', z', hx'z', hx', rfl⟩
    exact
      ⟨hlink.edge_mem, contractVertexMap u w z', hlink,
        (color_contractVertexMap hc z').trans hcz'⟩

/-- In the closed-trail branch no vertices are identified, so each new raw
fibre is the corresponding old fibre with the trail pair removed. -/
theorem rawColoredFiberEdges_smoothAndCollapse_of_eq
    {α β γ : Type*} {F : Graph α β} {color : α → γ}
    {e₁ e₂ : β} {u v w x : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w) (huw : u = w) :
    rawColoredFiberEdges
        (smoothAndCollapse F h₁ h₂ hne) color x y =
      rawColoredFiberEdges F color x y \ {e₁, e₂} := by
  subst w
  ext f
  rw [mem_rawColoredFiberEdges_smoothAndCollapse_iff h₁ h₂ hne hc]
  simp only [contractVertexMap_self, id_eq]
  constructor
  · rintro ⟨hf₁, hf₂, x', z', hx'z', rfl, hcz'⟩
    exact
      ⟨⟨hx'z'.edge_mem, z', hx'z', hcz'⟩, by simp [hf₁, hf₂]⟩
  · rintro ⟨⟨_, z, hxz, hcz⟩, hpair⟩
    have hf₁ : f ≠ e₁ := by
      intro hf
      apply hpair
      simp [hf]
    have hf₂ : f ≠ e₂ := by
      intro hf
      apply hpair
      simp [hf]
    exact ⟨hf₁, hf₂, x, z, hxz, rfl, hcz⟩

/-- The raw fibre at the retained representative is the union of the two old
outer-endpoint fibres, with the trail pair removed. -/
theorem rawColoredFiberEdges_smoothAndCollapse_retained
    {α β γ : Type*} {F : Graph α β} {color : α → γ}
    {e₁ e₂ : β} {u v w : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w) :
    rawColoredFiberEdges
        (smoothAndCollapse F h₁ h₂ hne) color u y =
      (rawColoredFiberEdges F color u y ∪
        rawColoredFiberEdges F color w y) \ {e₁, e₂} := by
  ext f
  rw [mem_rawColoredFiberEdges_smoothAndCollapse_iff h₁ h₂ hne hc]
  constructor
  · rintro ⟨hf₁, hf₂, x', z', hx'z', hqx', hcz'⟩
    have hx' : x' = u ∨ x' = w :=
      contractVertexMap_eq_retained_iff.mp hqx'
    refine ⟨?_, by simp [hf₁, hf₂]⟩
    rcases hx' with rfl | rfl
    · exact Or.inl ⟨hx'z'.edge_mem, z', hx'z', hcz'⟩
    · exact Or.inr ⟨hx'z'.edge_mem, z', hx'z', hcz'⟩
  · rintro ⟨hold, hpair⟩
    have hf₁ : f ≠ e₁ := by
      intro hf
      apply hpair
      simp [hf]
    have hf₂ : f ≠ e₂ := by
      intro hf
      apply hpair
      simp [hf]
    rcases hold with
      ⟨_, z, hz, hcz⟩ | ⟨_, z, hz, hcz⟩
    · exact ⟨hf₁, hf₂, u, z, hz, by simp, hcz⟩
    · exact ⟨hf₁, hf₂, w, z, hz, by simp, hcz⟩

/-- Away from the two contraction representatives, a raw fibre is simply
transported and has the trail pair removed. -/
theorem rawColoredFiberEdges_smoothAndCollapse_of_ne
    {α β γ : Type*} {F : Graph α β} {color : α → γ}
    {e₁ e₂ : β} {u v w x : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w)
    (hxu : x ≠ u) (hxw : x ≠ w) :
    rawColoredFiberEdges
        (smoothAndCollapse F h₁ h₂ hne) color x y =
      rawColoredFiberEdges F color x y \ {e₁, e₂} := by
  ext f
  rw [mem_rawColoredFiberEdges_smoothAndCollapse_iff h₁ h₂ hne hc]
  constructor
  · rintro ⟨hf₁, hf₂, x', z', hx'z', hqx', hcz'⟩
    have hx' : x' = x := by
      have hm :=
        congrArg (fun q ↦ q ∈ ({x} : Set α)) hqx'
      have hpre :
          x' ∈ contractVertexMap u w ⁻¹' ({x} : Set α) := by
        simpa using hm
      rw [preimage_contractVertexMap_singleton_of_ne hxu hxw] at hpre
      simpa using hpre
    subst x'
    exact
      ⟨⟨hx'z'.edge_mem, z', hx'z', hcz'⟩, by simp [hf₁, hf₂]⟩
  · rintro ⟨⟨_, z, hxz, hcz⟩, hpair⟩
    have hf₁ : f ≠ e₁ := by
      intro hf
      apply hpair
      simp [hf]
    have hf₂ : f ≠ e₂ := by
      intro hf
      apply hpair
      simp [hf]
    exact
      ⟨hf₁, hf₂, x, z, hxz,
        by simp [contractVertexMap_of_ne hxw], hcz⟩

/-- In a closed length-two trail the two removed edge copies have identical
membership in every coloured raw fibre. -/
theorem trail_pair_mem_rawColoredFiberEdges_iff_of_eq
    {α β γ : Type*} {F : Graph α β} {color : α → γ}
    {e₁ e₂ : β} {u v w x : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w) (huw : u = w) :
    e₁ ∈ rawColoredFiberEdges F color x y ↔
      e₂ ∈ rawColoredFiberEdges F color x y := by
  subst w
  rw [mem_rawColoredFiberEdges_iff_of_isLink h₁,
    mem_rawColoredFiberEdges_iff_of_isLink h₂]
  tauto

/-- Away from the outer endpoints, the two removed edge copies have identical
membership in every raw fibre because their other outer endpoints have the
same colour. -/
theorem trail_pair_mem_rawColoredFiberEdges_iff_of_ne
    {α β γ : Type*} {F : Graph α β} {color : α → γ}
    {e₁ e₂ : β} {u v w x : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hc : color u = color w) (hxu : x ≠ u) (hxw : x ≠ w) :
    e₁ ∈ rawColoredFiberEdges F color x y ↔
      e₂ ∈ rawColoredFiberEdges F color x y := by
  rw [mem_rawColoredFiberEdges_iff_of_isLink h₁,
    mem_rawColoredFiberEdges_iff_of_isLink h₂]
  constructor
  · rintro (⟨hxu', _⟩ | ⟨hxv, hcu⟩)
    · exact (hxu hxu').elim
    · exact Or.inl ⟨hxv, hc ▸ hcu⟩
  · rintro (⟨hxv, hcw⟩ | ⟨hxw', _⟩)
    · exact Or.inr ⟨hxv, hc.trans hcw⟩
    · exact (hxw hxw').elim

namespace WeightedParityState

variable
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite α] [Finite β]
    {color : α → γ}

/-- Raw fibres at distinct same-colour vertices are disjoint.  Otherwise a
common edge would map to a loop in the simple target. -/
theorem disjoint_rawColoredFiberEdges_of_same_color
    (S : WeightedParityState F G color)
    {u w : α} (huw : u ≠ w) (hc : color u = color w) (y : γ) :
    Disjoint (rawColoredFiberEdges F color u y)
      (rawColoredFiberEdges F color w y) := by
  rw [Set.disjoint_left]
  intro e heu hew
  rcases heu with ⟨_, a, hua, _⟩
  rcases hew with ⟨_, b, hwb, _⟩
  rcases hua.eq_and_eq_or_eq_and_eq hwb with hsame | hswap
  · exact (huw hsame.1).elim
  · have hadj := S.map_isLink hua
    rw [hswap.2, hc] at hadj
    exact G.irrefl hadj

/-- At the retained representative, membership of the first removed edge in
the union of the old raw fibres is equivalent to membership of the second. -/
theorem trail_pair_mem_union_rawColoredFiberEdges_iff
    (S : WeightedParityState F G color)
    {e₁ e₂ : β} {u v w : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (huw : u ≠ w) (hc : color u = color w) :
    e₁ ∈ (rawColoredFiberEdges F color u y ∪
        rawColoredFiberEdges F color w y) ↔
      e₂ ∈ (rawColoredFiberEdges F color u y ∪
        rawColoredFiberEdges F color w y) := by
  have huv : u ≠ v := by
    intro h
    subst v
    exact G.irrefl (S.map_isLink h₁)
  have hvw : v ≠ w := by
    intro h
    subst w
    exact G.irrefl (S.map_isLink h₂)
  simp only [Set.mem_union]
  rw [mem_rawColoredFiberEdges_iff_of_isLink h₁,
    mem_rawColoredFiberEdges_iff_of_isLink h₁,
    mem_rawColoredFiberEdges_iff_of_isLink h₂,
    mem_rawColoredFiberEdges_iff_of_isLink h₂]
  simp [huw, huw.symm, huv, hvw.symm, hc]

/-! ## The fused weight -/

/-- Merge the weights at the two outer endpoints.  In the loop branch the
weight is unchanged; in the contraction branch `w` is set to zero and its
weight is added to the retained representative `u`. -/
noncomputable def fusedWeight
    (S : WeightedParityState F G color) (u w : α) : α → ZMod 2 := by
  classical
  by_cases huw : u = w
  · exact S.weight
  · exact Function.update (Function.update S.weight w 0) u
      (S.weight u + S.weight w)

@[simp]
theorem fusedWeight_of_eq
    (S : WeightedParityState F G color) {u w : α} (huw : u = w) :
    S.fusedWeight u w = S.weight := by
  simp [fusedWeight, huw]

@[simp]
theorem fusedWeight_retained
    (S : WeightedParityState F G color) {u w : α} (huw : u ≠ w) :
    S.fusedWeight u w u = S.weight u + S.weight w := by
  simp [fusedWeight, huw]

@[simp]
theorem fusedWeight_removed
    (S : WeightedParityState F G color) {u w : α} (huw : u ≠ w) :
    S.fusedWeight u w w = 0 := by
  simp [fusedWeight, huw, huw.symm]

@[simp]
theorem fusedWeight_of_ne
    (S : WeightedParityState F G color) {u w x : α}
    (hxu : x ≠ u) (hxw : x ≠ w) :
    S.fusedWeight u w x = S.weight x := by
  by_cases huw : u = w <;>
    simp [fusedWeight, huw, hxu, hxw]

/-- Fusing two same-colour vertices preserves the total weight in every
target-vertex fibre. -/
theorem fiberWeightSum_fusedWeight
    (S : WeightedParityState F G color)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w) (y : γ) :
    fiberWeightSum (smoothAndCollapse F h₁ h₂ hne) color
        (S.fusedWeight u w) y =
      fiberWeightSum F color S.weight y := by
  classical
  by_cases huw : u = w
  · unfold fiberWeightSum
    apply Finset.sum_congr
    · ext x
      simp [vertexSet_smoothAndCollapse_of_eq F h₁ h₂ hne huw]
    · intro x hx
      rw [S.fusedWeight_of_eq huw]
  · let H := smoothAndCollapse F h₁ h₂ hne
    let live : Finset α := (Set.toFinite F.vertexSet).toFinset
    let f : α → ZMod 2 :=
      fun x ↦ if color x = y then S.weight x else 0
    let b : ZMod 2 :=
      if color u = y then S.weight u + S.weight w else 0
    have hu : u ∈ live := by
      simp [live, h₁.left_mem]
    have hw : w ∈ live := by
      simp [live, h₂.right_mem]
    have hu' : u ∈ live.erase w := by
      simp [hu, huw]
    have hsets :
        (Set.toFinite H.vertexSet).toFinset = live.erase w := by
      ext x
      simp [H, live,
        vertexSet_smoothAndCollapse_of_ne F h₁ h₂ hne huw, and_comm]
    have hterm (x : α) (hx : x ∈ live.erase w) :
        (if color x = y then S.fusedWeight u w x else 0) =
          Function.update f u b x := by
      have hxw : x ≠ w := by
        simpa using (Finset.mem_erase.mp hx).1
      by_cases hxu : x = u
      · subst x
        simp [f, b, huw]
      · simp [f, b, hxu, hxw]
    have hb : b = f u + f w := by
      by_cases hcy : color u = y
      · have hcwy : color w = y := hc ▸ hcy
        simp [b, f, hcy, hcwy]
      · have hcwy : color w ≠ y := by
          intro h
          exact hcy (hc.trans h)
        simp [b, f, hcy, hcwy]
    unfold fiberWeightSum
    change
      (∑ x ∈ (Set.toFinite H.vertexSet).toFinset,
        if color x = y then S.fusedWeight u w x else 0) = _
    rw [hsets]
    calc
      (∑ x ∈ live.erase w,
          if color x = y then S.fusedWeight u w x else 0) =
          ∑ x ∈ live.erase w, Function.update f u b x := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hterm x hx
      _ = b + ∑ x ∈ (live.erase w) \ {u}, f x :=
        Finset.sum_update_of_mem hu' f b
      _ = (f u + f w) +
          ∑ x ∈ (live.erase w).erase u, f x := by
        rw [hb]
        congr 2
        ext x
        simp [and_comm]
      _ = ∑ x ∈ live, f x := by
        have hw_sum := Finset.sum_erase_add live f hw
        have hu_sum := Finset.sum_erase_add (live.erase w) f hu'
        rw [← hw_sum, ← hu_sum]
        ring
      _ = ∑ x ∈ (Set.toFinite F.vertexSet).toFinset,
          if color x = y then S.weight x else 0 := rfl

/-! ## Parity preservation and the local state -/

/-- Raw-degree parity is unchanged in the closed-trail branch. -/
theorem cast_rawColoredFiberDegree_smoothAndCollapse_of_eq
    (_S : WeightedParityState F G color)
    {e₁ e₂ : β} {u v w x : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w) (huw : u = w) :
    (rawColoredFiberDegree
        (smoothAndCollapse F h₁ h₂ hne) color x y : ZMod 2) =
      (rawColoredFiberDegree F color x y : ZMod 2) := by
  unfold rawColoredFiberDegree
  rw [rawColoredFiberEdges_smoothAndCollapse_of_eq
    h₁ h₂ hne hc huw]
  exact cast_ncard_sdiff_pair_eq hne
    (trail_pair_mem_rawColoredFiberEdges_iff_of_eq h₁ h₂ huw)

/-- Raw-degree parity is unchanged away from the contraction
representatives. -/
theorem cast_rawColoredFiberDegree_smoothAndCollapse_of_ne
    (_S : WeightedParityState F G color)
    {e₁ e₂ : β} {u v w x : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w)
    (hxu : x ≠ u) (hxw : x ≠ w) :
    (rawColoredFiberDegree
        (smoothAndCollapse F h₁ h₂ hne) color x y : ZMod 2) =
      (rawColoredFiberDegree F color x y : ZMod 2) := by
  unfold rawColoredFiberDegree
  rw [rawColoredFiberEdges_smoothAndCollapse_of_ne
    h₁ h₂ hne hc hxu hxw]
  exact cast_ncard_sdiff_pair_eq hne
    (trail_pair_mem_rawColoredFiberEdges_iff_of_ne h₁ h₂ hc hxu hxw)

/-- At the retained representative, the new raw-degree parity is the sum of
the two old outer-endpoint parities. -/
theorem cast_rawColoredFiberDegree_smoothAndCollapse_retained
    (S : WeightedParityState F G color)
    {e₁ e₂ : β} {u v w : α} {y : γ}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w) (huw : u ≠ w) :
    (rawColoredFiberDegree
        (smoothAndCollapse F h₁ h₂ hne) color u y : ZMod 2) =
      (rawColoredFiberDegree F color u y : ZMod 2) +
        (rawColoredFiberDegree F color w y : ZMod 2) := by
  unfold rawColoredFiberDegree
  rw [rawColoredFiberEdges_smoothAndCollapse_retained h₁ h₂ hne hc]
  calc
    ((((rawColoredFiberEdges F color u y ∪
        rawColoredFiberEdges F color w y) \ {e₁, e₂}).ncard : ℕ) :
          ZMod 2) =
        (((rawColoredFiberEdges F color u y ∪
          rawColoredFiberEdges F color w y).ncard : ℕ) : ZMod 2) := by
      exact cast_ncard_sdiff_pair_eq hne
        (S.trail_pair_mem_union_rawColoredFiberEdges_iff
          h₁ h₂ huw hc)
    _ = ((rawColoredFiberEdges F color u y).ncard : ZMod 2) +
          ((rawColoredFiberEdges F color w y).ncard : ZMod 2) :=
      cast_ncard_union_eq_add
        (S.disjoint_rawColoredFiberEdges_of_same_color huw hc y)

/-- The weighted parity state produced by one fused smoothing move. -/
noncomputable def smoothAndCollapseState
    (S : WeightedParityState F G color)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : F.IsLink e₁ u v) (h₂ : F.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hc : color u = color w) :
    WeightedParityState (smoothAndCollapse F h₁ h₂ hne) G color where
  weight := S.fusedWeight u w
  weight_eq_zero_of_not_mem := by
    intro x hx
    by_cases huw : u = w
    · rw [S.fusedWeight_of_eq huw]
      apply S.weight_eq_zero_of_not_mem
      intro hxF
      apply hx
      rw [vertexSet_smoothAndCollapse_of_eq F h₁ h₂ hne huw]
      exact hxF
    · by_cases hxw : x = w
      · subst x
        exact S.fusedWeight_removed huw
      · have hxF : x ∉ F.vertexSet := by
          intro hxF
          apply hx
          rw [vertexSet_smoothAndCollapse_of_ne F h₁ h₂ hne huw]
          exact ⟨hxF, by simpa using hxw⟩
        have hxu : x ≠ u := by
          intro hxu
          subst x
          exact hxF h₁.left_mem
        rw [S.fusedWeight_of_ne hxu hxw]
        exact S.weight_eq_zero_of_not_mem hxF
  map_isLink := by
    intro e x y hxy
    rw [isLink_smoothAndCollapse] at hxy
    rcases hxy with ⟨_, _, x', y', hx'y', hx', hy'⟩
    have hadj := S.map_isLink hx'y'
    rw [← hx', ← hy', color_contractVertexMap hc,
      color_contractVertexMap hc]
    exact hadj
  fiber_weight_sum := by
    intro y
    rw [S.fiberWeightSum_fusedWeight h₁ h₂ hne hc y]
    exact S.fiber_weight_sum y
  degree_parity := by
    intro x hx y hxy
    by_cases huw : u = w
    · rw [S.cast_rawColoredFiberDegree_smoothAndCollapse_of_eq
        h₁ h₂ hne hc huw, S.fusedWeight_of_eq huw]
      have hxF : x ∈ F.vertexSet := by
        rw [vertexSet_smoothAndCollapse_of_eq F h₁ h₂ hne huw] at hx
        exact hx
      exact S.degree_parity x hxF hxy
    · by_cases hxu : x = u
      · subst x
        rw [S.cast_rawColoredFiberDegree_smoothAndCollapse_retained
          h₁ h₂ hne hc huw, S.fusedWeight_retained huw]
        have huF := h₁.left_mem
        have hwF := h₂.right_mem
        have hwy : G.Adj (color w) y := by
          rw [← hc]
          exact hxy
        rw [S.degree_parity u huF hxy, S.degree_parity w hwF hwy]
      · have hxw : x ≠ w := by
          intro hxw
          subst x
          have :
              w ∈ F.vertexSet \ ({w} : Set α) := by
            rw [← vertexSet_smoothAndCollapse_of_ne
              F h₁ h₂ hne huw]
            exact hx
          exact this.2 rfl
        rw [S.cast_rawColoredFiberDegree_smoothAndCollapse_of_ne
          h₁ h₂ hne hc hxu hxw, S.fusedWeight_of_ne hxu hxw]
        have hxF : x ∈ F.vertexSet := by
          have :
              x ∈ F.vertexSet \ ({w} : Set α) := by
            rw [← vertexSet_smoothAndCollapse_of_ne
              F h₁ h₂ hne huw]
            exact hx
          exact this.1
        exact S.degree_parity x hxF hxy

/-! ## A decreasing normalizer -/

/-- Data selected from a raw coloured fibre of degree greater than one.

The two edge identities are distinct, both are incident with the violating
vertex `v`, and their other endpoints have the same colour.  Thus they are
exactly the input required by `smoothAndCollapseState`. -/
structure ViolatingFiberPair
    {F : Graph α β} (S : WeightedParityState F G color) where
  e₁ : β
  e₂ : β
  u : α
  v : α
  w : α
  first_isLink : F.IsLink e₁ u v
  second_isLink : F.IsLink e₂ v w
  edge_ne : e₁ ≠ e₂
  color_eq : color u = color w

/-- Every non-reduced state contains a pair of distinct edge copies suitable
for one fused smoothing move. -/
theorem nonempty_violatingFiberPair
    {F : Graph α β} (S : WeightedParityState F G color)
    (hred : ¬ S.IsFiberReduced) :
    Nonempty (ViolatingFiberPair S) := by
  classical
  unfold IsFiberReduced at hred
  push Not at hred
  obtain ⟨v, hv, y, hadj, hlarge⟩ := hred
  obtain ⟨e₁, e₂, he₁, he₂, hne⟩ :=
    (Set.one_lt_ncard_iff
      (finite_rawColoredFiberEdges color v y)).mp hlarge
  rcases he₁ with ⟨_, u, hvu, hcu⟩
  rcases he₂ with ⟨_, w, hvw, hcw⟩
  exact
    ⟨⟨e₁, e₂, u, v, w, hvu.symm, hvw, hne,
      hcu.trans hcw.symm⟩⟩

/-- A fixed classical choice of a violating pair.  Keeping the choice in a
named definition makes the recursive normalizer's decreasing call explicit. -/
noncomputable def violatingFiberPair
    {F : Graph α β} (S : WeightedParityState F G color)
    (hred : ¬ S.IsFiberReduced) :
    ViolatingFiberPair S :=
  Classical.choice (nonempty_violatingFiberPair S hred)

/-- Exported result of the fibre-degree normalizer.

The ambient vertex and edge types, and hence the ambient colouring, stay
fixed.  The graph and state change, the graph is certified to be a split-off
minor of the input, and the terminal state has every adjacent raw fibre degree
at most one. -/
structure FiberReductionResult
    (F : Graph α β) (G : SimpleGraph γ) (color : α → γ) where
  graph : Graph α β
  state : WeightedParityState graph G color
  isSplitOffMinor : IsSplitOffMinor graph F
  reduced : state.IsFiberReduced

/-- Direct form of the terminal bound, provided as a stable API for clients
that do not otherwise need the `IsFiberReduced` predicate. -/
theorem FiberReductionResult.degree_le_one
    {F : Graph α β}
    (R : FiberReductionResult F G color)
    (x : α) (hx : x ∈ R.graph.vertexSet) {y : γ}
    (hxy : G.Adj (color x) y) :
    rawColoredFiberDegree R.graph color x y ≤ 1 :=
  R.reduced x hx hxy

/-- Repeatedly fuse a pair from a raw coloured fibre of degree greater than
one.  Each recursive call removes exactly two live edge copies, so
`F.edgeSet.ncard` is a strictly decreasing well-founded measure. -/
noncomputable def normalizeFiberDegrees
    (F : Graph α β) (S : WeightedParityState F G color) :
    FiberReductionResult F G color := by
  classical
  by_cases hred : S.IsFiberReduced
  · exact ⟨F, S, .refl F, hred⟩
  · let W := violatingFiberPair S hred
    let H :=
      smoothAndCollapse F W.first_isLink W.second_isLink W.edge_ne
    let T : WeightedParityState H G color :=
      S.smoothAndCollapseState W.first_isLink W.second_isLink
        W.edge_ne W.color_eq
    let R := normalizeFiberDegrees H T
    exact
      { graph := R.graph
        state := R.state
        isSplitOffMinor :=
          R.isSplitOffMinor.trans
            (smoothAndCollapse_isSplitOffMinor F W.first_isLink
              W.second_isLink W.edge_ne)
        reduced := R.reduced }
termination_by F.edgeSet.ncard
decreasing_by
  exact
    ncard_edgeSet_smoothAndCollapse_lt F W.first_isLink
      W.second_isLink W.edge_ne (Set.toFinite F.edgeSet)

end WeightedParityState

end StrongRoberson
