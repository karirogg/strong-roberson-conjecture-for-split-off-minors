import StrongRoberson.Proof.Operations

/-!
# Contracting everything outside a protected vertex set

This file packages the contraction phase used near the end of the lift proof.
Starting from an edge-typed graph `F` and a set `B` of protected live
vertices, we repeatedly contract a non-loop edge whose two endpoints lie
outside `B`.  The trace records the composite map from original vertices to
their final representatives.

The trace is deliberately explicit.  It exposes the invariants needed by the
paper proof:

* vertices of `B` are fixed, hence remain pairwise distinct;
* an edge incident with `B` is never selected for contraction and survives
  with its protected endpoint unchanged; and
* vertices joined by a path entirely outside `B` acquire the same final
  representative.

Edge identities are never relabelled.  Each contraction deletes only its
selected edge copy.
-/

namespace StrongRoberson

universe u

/-- A graph is reduced outside `B` when every live edge with both endpoints
outside `B` is a loop. -/
def OutsideReduced {α β : Type*} (G : Graph α β) (B : Set α) : Prop :=
  ∀ ⦃e x y⦄, G.IsLink e x y → x ∉ B → y ∉ B → x = y

/-- A finite trace of non-loop contractions performed wholly outside `B`.

The function in the final index maps every original ambient vertex to its
representative in the final graph.  It is total on the ambient type, although
the useful membership theorem below is stated for live original vertices.
-/
inductive CollapseOutsideTrace {α β : Type u} (B : Set α) :
    Graph α β → Graph α β → (α → α) → Prop where
  | refl (F : Graph α β) :
      CollapseOutsideTrace B F F id
  | contract {F K : Graph α β} {ρ : α → α}
      {e : β} {u v : α}
      (he : F.IsLink e u v) (hne : u ≠ v)
      (hu : u ∉ B) (hv : v ∉ B)
      (tail :
        CollapseOutsideTrace B (contractEdge F he hne) K ρ) :
      CollapseOutsideTrace B F K
        (ρ ∘ contractVertexMap u v)

namespace CollapseOutsideTrace

variable {α β : Type u} {B : Set α}
  {F K : Graph α β} {ρ : α → α}

/-- One contraction retaining an outside vertex maps outside vertices to
outside vertices. -/
theorem contractVertexMap_not_mem {u v x : α}
    (hu : u ∉ B) (hx : x ∉ B) :
    contractVertexMap u v x ∉ B := by
  by_cases hxv : x = v
  · subst x
    simpa using hu
  · simpa [contractVertexMap_of_ne hxv] using hx

/-- Every protected vertex is fixed by the composite representative map. -/
theorem protected_fixed
    (t : CollapseOutsideTrace B F K ρ) {b : α} (hb : b ∈ B) :
    ρ b = b := by
  induction t generalizing b with
  | refl => rfl
  | @contract F K ρ e u v he hne hu hv tail ih =>
      have hbv : b ≠ v := by
        intro h
        subst b
        exact hv hb
      change ρ (contractVertexMap u v b) = b
      rw [contractVertexMap_of_ne hbv]
      exact ih hb

/-- Distinct protected vertices have distinct final representatives. -/
theorem protected_injective
    (t : CollapseOutsideTrace B F K ρ)
    {b c : α} (hb : b ∈ B) (hc : c ∈ B) (hbc : b ≠ c) :
    ρ b ≠ ρ c := by
  rw [t.protected_fixed hb, t.protected_fixed hc]
  exact hbc

/-- An outside vertex always has an outside final representative. -/
theorem outside_not_mem
    (t : CollapseOutsideTrace B F K ρ) {x : α} (hx : x ∉ B) :
    ρ x ∉ B := by
  induction t generalizing x with
  | refl => exact hx
  | @contract F K ρ e u v he hne hu hv tail ih =>
      exact ih (contractVertexMap_not_mem hu hx)

/-- Live original vertices map to live vertices of the final graph. -/
theorem representative_mem
    (t : CollapseOutsideTrace B F K ρ)
    {x : α} (hx : x ∈ F.vertexSet) :
    ρ x ∈ K.vertexSet := by
  induction t generalizing x with
  | refl => exact hx
  | @contract F K ρ e u v he hne hu hv tail ih =>
      change ρ (contractVertexMap u v x) ∈ K.vertexSet
      apply ih
      rw [vertexSet_contractEdge]
      exact
        ⟨contractVertexMap_mem he.left_mem hx,
          contractVertexMap_ne_removed hne x⟩

/-- A contraction trace is a split-off-minor certificate. -/
theorem isSplitOffMinor
    (t : CollapseOutsideTrace B F K ρ) :
    IsSplitOffMinor K F := by
  induction t with
  | refl => exact .refl _
  | @contract F K ρ e u v he hne hu hv tail ih =>
      exact .trans ih (.contract F he hne)

/-- Every original edge either survives between the representatives of its
original endpoints, or its two endpoint representatives have already merged.
-/
theorem isLink_or_representatives_eq
    (t : CollapseOutsideTrace B F K ρ)
    {e : β} {x y : α} (hxy : F.IsLink e x y) :
    K.IsLink e (ρ x) (ρ y) ∨ ρ x = ρ y := by
  induction t generalizing e x y with
  | refl =>
      exact Or.inl hxy
  | @contract F K ρ e₀ u v he hne hu hv tail ih =>
      change
        K.IsLink e
            (ρ (contractVertexMap u v x))
            (ρ (contractVertexMap u v y)) ∨
          ρ (contractVertexMap u v x) =
            ρ (contractVertexMap u v y)
      by_cases hee : e = e₀
      · subst e
        right
        rcases he.eq_and_eq_or_eq_and_eq hxy with h | h
        · rcases h with ⟨rfl, rfl⟩
          simp [hne]
        · rcases h with ⟨rfl, rfl⟩
          simp [hne]
      · exact ih
          (StrongRoberson.Graph.IsLink.contractEdge
            he hne hxy hee)

/-- An original edge incident with a protected vertex survives every outside
contraction, with that protected endpoint unchanged. -/
theorem boundary_isLink
    (t : CollapseOutsideTrace B F K ρ)
    {e : β} {b x : α} (hb : b ∈ B) (hbx : F.IsLink e b x) :
    K.IsLink e b (ρ x) := by
  induction t generalizing e b x with
  | refl =>
      exact hbx
  | @contract F K ρ e₀ u v he hne hu hv tail ih =>
      have hee : e ≠ e₀ := by
        intro h
        subst e
        rcases he.eq_and_eq_or_eq_and_eq hbx with h | h
        · apply hu
          rw [h.1]
          exact hb
        · apply hv
          rw [h.2]
          exact hb
      have hbv : b ≠ v := by
        intro h
        subst b
        exact hv hb
      have hnext :=
        StrongRoberson.Graph.IsLink.contractEdge
          he hne hbx hee
      rw [contractVertexMap_of_ne hbv] at hnext
      exact ih hb hnext

end CollapseOutsideTrace

/-- Connectivity by a finite path all of whose vertices lie outside `B`.
The edge copies on successive steps are kept explicit. -/
inductive OutsideConnected {α β : Type*}
    (F : Graph α β) (B : Set α) : α → α → Prop where
  | refl {x : α} (hx : x ∉ B) :
      OutsideConnected F B x x
  | tail {x y z : α} {e : β}
      (hxy : OutsideConnected F B x y)
      (hyz : F.IsLink e y z) (hz : z ∉ B) :
      OutsideConnected F B x z

namespace OutsideConnected

variable {α β : Type*} {F : Graph α β} {B : Set α}
  {x y z : α}

theorem left_not_mem (h : OutsideConnected F B x y) :
    x ∉ B := by
  induction h with
  | refl hx => exact hx
  | tail _ _ _ ih => exact ih

theorem right_not_mem (h : OutsideConnected F B x y) :
    y ∉ B := by
  induction h with
  | refl hx => exact hx
  | tail _ _ hz _ => exact hz

end OutsideConnected

/-- The terminating contraction recursion.  Finiteness of the live edge set is
enough: every recursive call deletes exactly the selected edge copy. -/
private theorem exists_collapseOutsideTraceAux {α β : Type u}
    (F : Graph α β) (B : Set α) (hfinite : F.edgeSet.Finite) :
    ∃ K ρ,
      CollapseOutsideTrace B F K ρ ∧ OutsideReduced K B := by
  classical
  by_cases hstep :
      ∃ e u v, F.IsLink e u v ∧ u ∉ B ∧ v ∉ B ∧ u ≠ v
  · obtain ⟨e, u, v, he, hu, hv, hne⟩ := hstep
    let F' := contractEdge F he hne
    have hfinite' : F'.edgeSet.Finite := by
      dsimp only [F']
      rw [edgeSet_contractEdge]
      exact hfinite.sdiff
    obtain ⟨K, ρ, ht, hred⟩ :=
      exists_collapseOutsideTraceAux F' B hfinite'
    exact
      ⟨K, ρ ∘ contractVertexMap u v,
        .contract he hne hu hv ht, hred⟩
  · exact
      ⟨F, id, .refl F, by
        intro e x y he hx hy
        by_contra hxy
        exact hstep ⟨e, x, y, he, hx, hy, hxy⟩⟩
  termination_by F.edgeSet.ncard
  decreasing_by
    exact ncard_edgeSet_contractEdge_lt F he hne hfinite

/-- Existence form of the complete outside-contraction construction. -/
theorem exists_collapseOutsideTrace {α β : Type u}
    (F : Graph α β) (B : Set α) (hfinite : F.edgeSet.Finite) :
    ∃ K ρ,
      CollapseOutsideTrace B F K ρ ∧ OutsideReduced K B := by
  exact exists_collapseOutsideTraceAux F B hfinite

/-- The output of completely contracting non-loop edges outside `B`. -/
structure CollapseOutsideResult {α β : Type u}
    (F : Graph α β) (B : Set α) where
  graph : Graph α β
  representative : α → α
  trace :
    CollapseOutsideTrace B F graph representative
  reduced : OutsideReduced graph B
  protected_live : B ⊆ F.vertexSet

namespace CollapseOutsideResult

variable {α β : Type u} {F : Graph α β} {B : Set α}

/-- The terminal outside-collapse result exists whenever the live edge set is
finite and the protected set consists of live original vertices. -/
theorem nonempty (F : Graph α β) (B : Set α)
    (hB : B ⊆ F.vertexSet) (hfinite : F.edgeSet.Finite) :
    Nonempty (CollapseOutsideResult F B) := by
  obtain ⟨K, ρ, ht, hred⟩ :=
    exists_collapseOutsideTrace F B hfinite
  exact ⟨⟨K, ρ, ht, hred, hB⟩⟩

/-- Choose the terminal graph and its representative map. -/
noncomputable def collapseOutside (F : Graph α β) (B : Set α)
    (hB : B ⊆ F.vertexSet) [Finite F.edgeSet] :
    CollapseOutsideResult F B :=
  Classical.choice
    (nonempty F B hB (Set.toFinite F.edgeSet))

theorem isSplitOffMinor (r : CollapseOutsideResult F B) :
    IsSplitOffMinor r.graph F :=
  r.trace.isSplitOffMinor

@[simp]
theorem protected_fixed (r : CollapseOutsideResult F B)
    {b : α} (hb : b ∈ B) :
    r.representative b = b :=
  r.trace.protected_fixed hb

theorem protected_injective (r : CollapseOutsideResult F B)
    {b c : α} (hb : b ∈ B) (hc : c ∈ B) (hbc : b ≠ c) :
    r.representative b ≠ r.representative c :=
  r.trace.protected_injective hb hc hbc

theorem protected_mem (r : CollapseOutsideResult F B)
    {b : α} (hb : b ∈ B) :
    b ∈ r.graph.vertexSet := by
  rw [← r.protected_fixed hb]
  exact r.trace.representative_mem (r.protected_live hb)

theorem outside_not_mem (r : CollapseOutsideResult F B)
    {x : α} (hx : x ∉ B) :
    r.representative x ∉ B :=
  r.trace.outside_not_mem hx

theorem representative_mem (r : CollapseOutsideResult F B)
    {x : α} (hx : x ∈ F.vertexSet) :
    r.representative x ∈ r.graph.vertexSet :=
  r.trace.representative_mem hx

theorem boundary_isLink (r : CollapseOutsideResult F B)
    {e : β} {b x : α} (hb : b ∈ B) (hbx : F.IsLink e b x) :
    r.graph.IsLink e b (r.representative x) :=
  r.trace.boundary_isLink hb hbx

theorem boundary_edge_mem (r : CollapseOutsideResult F B)
    {e : β} {b x : α} (hb : b ∈ B) (hbx : F.IsLink e b x) :
    e ∈ r.graph.edgeSet :=
  (r.boundary_isLink hb hbx).edge_mem

theorem outside_edge_representatives_eq
    (r : CollapseOutsideResult F B)
    {e : β} {x y : α} (hxy : F.IsLink e x y)
    (hx : x ∉ B) (hy : y ∉ B) :
    r.representative x = r.representative y := by
  rcases r.trace.isLink_or_representatives_eq hxy with hsurvives | heq
  · exact r.reduced hsurvives
      (r.outside_not_mem hx) (r.outside_not_mem hy)
  · exact heq

/-- Vertices connected through original outside vertices acquire the same
final representative. -/
theorem outsideConnected_representative_eq
    (r : CollapseOutsideResult F B)
    {x y : α} (hxy : OutsideConnected F B x y) :
    r.representative x = r.representative y := by
  induction hxy with
  | refl => rfl
  | tail hxy hyz hz ih =>
      exact ih.trans
        (r.outside_edge_representatives_eq hyz hxy.right_not_mem hz)

end CollapseOutsideResult

end StrongRoberson
