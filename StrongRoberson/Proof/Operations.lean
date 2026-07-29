import StrongRoberson.SplitOff

/-!
# Closure lemmas for split-off minors

This file packages the elementary operational steps used throughout the paper
proof.  None of the graph operations or the `IsSplitOffMinor` relation are
changed here; these are only derived lemmas for composing their constructors.
-/

namespace StrongRoberson

universe u

/-- The vertex map used by `contractEdge`: `v` is identified with `u` and
every other ambient vertex is fixed. -/
noncomputable def contractVertexMap {α : Type*} (u v : α) : α → α := by
  classical
  exact Function.update id v u

@[simp]
theorem contractVertexMap_removed {α : Type*} (u v : α) :
    contractVertexMap u v v = u := by
  classical
  simp [contractVertexMap]

@[simp]
theorem contractVertexMap_of_ne {α : Type*} {u v x : α} (hxv : x ≠ v) :
    contractVertexMap u v x = x := by
  classical
  simp [contractVertexMap, hxv]

@[simp]
theorem contractVertexMap_self {α : Type*} (u : α) :
    contractVertexMap u u = id := by
  classical
  funext x
  by_cases hxu : x = u
  · subst x
    simp
  · simp [contractVertexMap, hxu]

/-- When `u` and `v` are distinct, no vertex is sent to the removed
representative `v`. -/
theorem contractVertexMap_ne_removed {α : Type*} {u v : α}
    (huv : u ≠ v) (x : α) :
    contractVertexMap u v x ≠ v := by
  by_cases hxv : x = v
  · subst x
    simpa using huv
  · simpa [contractVertexMap_of_ne hxv] using hxv

/-- The retained vertex `u` has precisely `u` and `v` as preimages under a
contraction. -/
@[simp]
theorem contractVertexMap_eq_retained_iff {α : Type*} {u v x : α} :
    contractVertexMap u v x = u ↔ x = u ∨ x = v := by
  by_cases hxv : x = v
  · subst x
    simp
  · simp [hxv]

/-- Set-theoretic form of `contractVertexMap_eq_retained_iff`. -/
theorem preimage_contractVertexMap_singleton_retained {α : Type*} {u v : α} :
    contractVertexMap u v ⁻¹' ({u} : Set α) = {u, v} := by
  ext x
  simp

/-- The removed representative has empty preimage under a nontrivial
contraction. -/
theorem preimage_contractVertexMap_singleton_removed {α : Type*} {u v : α}
    (huv : u ≠ v) :
    contractVertexMap u v ⁻¹' ({v} : Set α) = ∅ := by
  ext x
  simp [contractVertexMap_ne_removed huv]

/-- Every vertex distinct from both representatives has itself as its unique
preimage. -/
theorem preimage_contractVertexMap_singleton_of_ne {α : Type*}
    {u v x : α} (hxu : x ≠ u) (hxv : x ≠ v) :
    contractVertexMap u v ⁻¹' ({x} : Set α) = {x} := by
  ext y
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  by_cases hyv : y = v
  · subst y
    constructor
    · intro h
      rw [contractVertexMap_removed] at h
      exact (hxu h.symm).elim
    · intro h
      exact (hxv h.symm).elim
  · simp [hyv]

/-- The contraction map sends live vertices to live vertices whenever the
retained representative is live. -/
theorem contractVertexMap_mem {α : Type*} {u v x : α} {s : Set α}
    (hu : u ∈ s) (hx : x ∈ s) :
    contractVertexMap u v x ∈ s := by
  by_cases hxv : x = v
  · subst x
    simpa using hu
  · simpa [hxv] using hx

/-- Mapping a live vertex set by a nontrivial contraction removes exactly `v`,
provided the retained representative `u` was live. -/
theorem image_contractVertexMap_of_ne {α : Type*} {u v : α}
    {s : Set α} (hu : u ∈ s) (huv : u ≠ v) :
    contractVertexMap u v '' s = s \ {v} := by
  ext x
  simp only [Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor
    · by_cases hyv : y = v
      · subst y
        simpa using hu
      · simpa [contractVertexMap_of_ne hyv] using hy
    · exact contractVertexMap_ne_removed huv y
  · rintro ⟨hx, hxv⟩
    exact ⟨x, hx, contractVertexMap_of_ne hxv⟩

/-- Exact link characterization for `reattachEdge`. -/
@[simp]
theorem isLink_reattachEdge {α β : Type*} (G : Graph α β)
    (e f : β) (u v x y : α) (he : e ∈ G.edgeSet)
    (hu : u ∈ G.vertexSet) (hv : v ∈ G.vertexSet) :
    (reattachEdge G e u v he hu hv).IsLink f x y ↔
      (f = e ∧ s(x, y) = s(u, v)) ∨
        (f ≠ e ∧ G.IsLink f x y) :=
  Iff.rfl

/-- Exact link characterization for splitting off two incident edge copies.
The identity `e₁` is reused for the new edge from `u` to `w`. -/
@[simp]
theorem isLink_splitOff {α β : Type*} (G : Graph α β)
    {e₁ e₂ f : β} {u v w x y : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (splitOff G h₁ h₂ hne).IsLink f x y ↔
      (f = e₁ ∧ s(x, y) = s(u, w)) ∨
        (f ≠ e₁ ∧ f ≠ e₂ ∧ G.IsLink f x y) := by
  simp only [splitOff, isLink_reattachEdge, Graph.deleteEdges_isLink,
    Set.mem_singleton_iff]
  tauto

/-- The edge copy retained by `splitOff` has precisely the new endpoints. -/
theorem isLink_splitOff_new {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (splitOff G h₁ h₂ hne).IsLink e₁ u w := by
  rw [isLink_splitOff]
  exact Or.inl ⟨rfl, rfl⟩

/-- Exact link characterization for contraction. The contracted edge copy is
deleted and every other edge is mapped by `contractVertexMap`. -/
@[simp]
theorem isLink_contractEdge {α β : Type*} (G : Graph α β)
    {e f : β} {u v x y : α} (he : G.IsLink e u v) (hne : u ≠ v) :
    (contractEdge G he hne).IsLink f x y ↔
      f ≠ e ∧ ∃ x' y', G.IsLink f x' y' ∧
        contractVertexMap u v x' = x ∧ contractVertexMap u v y' = y := by
  classical
  simp only [contractEdge, Graph.deleteEdges_isLink, Graph.map_isLink,
    Set.mem_singleton_iff, Relation.Map, contractVertexMap]
  tauto

/-- Every noncontracted edge survives contraction after applying the vertex
identification map to its endpoints. -/
theorem Graph.IsLink.contractEdge {α β : Type*} {G : Graph α β}
    {e f : β} {u v x y : α} (he : G.IsLink e u v) (hne : u ≠ v)
    (hxy : G.IsLink f x y) (hfe : f ≠ e) :
    (contractEdge G he hne).IsLink f
      (contractVertexMap u v x) (contractVertexMap u v y) := by
  rw [isLink_contractEdge]
  exact ⟨hfe, x, y, hxy, rfl, rfl⟩

/-- Contracting `uv` removes exactly `v` from the live vertex set because `u`
is retained as the representative. -/
@[simp]
theorem vertexSet_contractEdge {α β : Type*} (G : Graph α β)
    {e : β} {u v : α} (he : G.IsLink e u v) (hne : u ≠ v) :
    (contractEdge G he hne).vertexSet = G.vertexSet \ {v} := by
  classical
  ext x
  simp only [contractEdge, Graph.vertexSet_deleteEdges, Graph.vertexSet_map,
    Set.mem_image, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor
    · rw [Function.update_apply]
      split <;> rename_i h
      · simpa [h] using he.left_mem
      · simpa using hy
    · rw [Function.update_apply]
      split <;> rename_i h
      · simpa [h] using hne
      · simpa using h
  · rintro ⟨hxG, hxv⟩
    refine ⟨x, hxG, ?_⟩
    rw [Function.update_apply]
    split <;> rename_i h
    · exact (hxv h).elim
    · rfl

/-- A split removes exactly one live edge copy. -/
theorem ncard_edgeSet_splitOff {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (splitOff G h₁ h₂ hne).edgeSet.ncard = G.edgeSet.ncard - 1 := by
  rw [edgeSet_splitOff, Set.ncard_sdiff_singleton_of_mem h₂.edge_mem]

/-- A contraction removes exactly one live edge copy. -/
theorem ncard_edgeSet_contractEdge {α β : Type*} (G : Graph α β)
    {e : β} {u v : α} (he : G.IsLink e u v) (hne : u ≠ v) :
    (contractEdge G he hne).edgeSet.ncard = G.edgeSet.ncard - 1 := by
  rw [edgeSet_contractEdge, Set.ncard_sdiff_singleton_of_mem he.edge_mem]

/-- A non-loop contraction removes exactly one live vertex. -/
theorem ncard_vertexSet_contractEdge {α β : Type*} (G : Graph α β)
    {e : β} {u v : α} (he : G.IsLink e u v) (hne : u ≠ v) :
    (contractEdge G he hne).vertexSet.ncard = G.vertexSet.ncard - 1 := by
  rw [vertexSet_contractEdge, Set.ncard_sdiff_singleton_of_mem he.right_mem]

/-- On a finite edge set, splitting strictly decreases the number of edges. -/
theorem ncard_edgeSet_splitOff_lt {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hfinite : G.edgeSet.Finite) :
    (splitOff G h₁ h₂ hne).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_splitOff]
  exact Set.ncard_sdiff_singleton_lt_of_mem h₂.edge_mem hfinite

/-- On a finite edge set, contraction strictly decreases the number of edges. -/
theorem ncard_edgeSet_contractEdge_lt {α β : Type*} (G : Graph α β)
    {e : β} {u v : α} (he : G.IsLink e u v) (hne : u ≠ v)
    (hfinite : G.edgeSet.Finite) :
    (contractEdge G he hne).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_contractEdge]
  exact Set.ncard_sdiff_singleton_lt_of_mem he.edge_mem hfinite

/-- On a finite vertex set, a non-loop contraction strictly decreases the
number of vertices. -/
theorem ncard_vertexSet_contractEdge_lt {α β : Type*} (G : Graph α β)
    {e : β} {u v : α} (he : G.IsLink e u v) (hne : u ≠ v)
    (hfinite : G.vertexSet.Finite) :
    (contractEdge G he hne).vertexSet.ncard < G.vertexSet.ncard := by
  rw [vertexSet_contractEdge]
  exact Set.ncard_sdiff_singleton_lt_of_mem he.right_mem hfinite

namespace IsSplitOffMinor

/-- Taking a subgraph is a split-off-minor step. -/
theorem of_le {α β : Type u} {H G : Graph α β} (h : H ≤ G) :
    IsSplitOffMinor H G :=
  .subgraph h

/-- Deleting any set of edges is a split-off-minor step. -/
theorem deleteEdges {α β : Type u} (G : Graph α β) (s : Set β) :
    IsSplitOffMinor (G.deleteEdges s) G :=
  .subgraph Graph.deleteEdges_le

/-- Restricting to any set of edges is a split-off-minor step. -/
theorem restrict {α β : Type u} (G : Graph α β) (s : Set β) :
    IsSplitOffMinor (G.restrict s) G :=
  .subgraph Graph.restrict_le

/-- Deleting any set of vertices is a split-off-minor step. -/
theorem deleteVerts {α β : Type u} (G : Graph α β) (s : Set α) :
    IsSplitOffMinor (G.deleteVerts s) G :=
  .subgraph Graph.deleteVerts_le

/-- Relabel the lower graph in a split-off-minor certificate. -/
theorem iso_left {α β γ δ ε ζ : Type u}
    {H : Graph α β} {H' : Graph γ δ} {G : Graph ε ζ}
    (i : GraphIso H H') (h : IsSplitOffMinor H' G) :
    IsSplitOffMinor H G :=
  .trans (.iso i) h

/-- Relabel the upper graph in a split-off-minor certificate. -/
theorem iso_right {α β γ δ ε ζ : Type u}
    {H : Graph α β} {G : Graph γ δ} {G' : Graph ε ζ}
    (h : IsSplitOffMinor H G) (i : GraphIso G G') :
    IsSplitOffMinor H G' :=
  .trans h (.iso i)

end IsSplitOffMinor

/-- Smooth the length-two trail `u -[e₁]- v -[e₂]- w`, then eliminate the new
edge `uw`. If `u ≠ w`, the edge is contracted, retaining `u`; if `u = w`, it
is a loop and is deleted.

In the paper this is useful when `u` and `w` lie in the same target-vertex
fibre. The definition itself does not need to mention that external labelling.
-/
noncomputable def smoothAndCollapse {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) : Graph α β := by
  classical
  by_cases huw : u = w
  · exact (splitOff G h₁ h₂ hne).deleteEdges {e₁}
  · exact contractEdge (splitOff G h₁ h₂ hne)
      (isLink_splitOff_new G h₁ h₂ hne) huw

/-- Uniform link characterization for `smoothAndCollapse`. Both branches of
the definition delete `e₁` and `e₂`; all remaining edges are transported by
the single endpoint-identification map `contractVertexMap u w`. When `u = w`,
that map is the identity. -/
@[simp]
theorem isLink_smoothAndCollapse {α β : Type*} (G : Graph α β)
    {e₁ e₂ f : β} {u v w x y : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (smoothAndCollapse G h₁ h₂ hne).IsLink f x y ↔
      f ≠ e₁ ∧ f ≠ e₂ ∧
        ∃ x' y', G.IsLink f x' y' ∧
          contractVertexMap u w x' = x ∧
          contractVertexMap u w y' = y := by
  classical
  unfold smoothAndCollapse
  split <;> rename_i huw
  · subst w
    simp [isLink_splitOff]
    tauto
  · rw [isLink_contractEdge]
    constructor
    · rintro ⟨hf₁, x', y', hxy, hx, hy⟩
      rw [isLink_splitOff] at hxy
      rcases hxy with hnew | hold
      · exact (hf₁ hnew.1).elim
      · exact ⟨hf₁, hold.2.1, x', y', hold.2.2, hx, hy⟩
    · rintro ⟨hf₁, hf₂, x', y', hxy, hx, hy⟩
      refine ⟨hf₁, x', y', ?_, hx, hy⟩
      exact (isLink_splitOff G h₁ h₂ hne).2
        (Or.inr ⟨hf₁, hf₂, hxy⟩)

/-- Smoothing and collapsing removes exactly the two edge copies in the
original length-two trail. -/
@[simp]
theorem edgeSet_smoothAndCollapse {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (smoothAndCollapse G h₁ h₂ hne).edgeSet =
      G.edgeSet \ {e₁, e₂} := by
  classical
  unfold smoothAndCollapse
  split <;> rename_i huw
  · simp only [Graph.edgeSet_deleteEdges, edgeSet_splitOff]
    ext f
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  · rw [edgeSet_contractEdge, edgeSet_splitOff]
    ext f
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto

/-- The compound smoothing operation preserves the vertex set when its new
edge is a loop. -/
@[simp]
theorem vertexSet_smoothAndCollapse_of_eq {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (huw : u = w) :
    (smoothAndCollapse G h₁ h₂ hne).vertexSet = G.vertexSet := by
  classical
  unfold smoothAndCollapse
  simp [huw]

/-- The compound smoothing operation removes `w` when its new edge is
non-loop and hence contracted with `u` retained. -/
@[simp]
theorem vertexSet_smoothAndCollapse_of_ne {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (huw : u ≠ w) :
    (smoothAndCollapse G h₁ h₂ hne).vertexSet =
      G.vertexSet \ {w} := by
  classical
  unfold smoothAndCollapse
  simp [huw]

/-- Algebraic normal form of the compound smoothing operation. Uniformly in
the loop and non-loop cases, it identifies `w` with `u` and deletes precisely
the two original trail edges. -/
theorem smoothAndCollapse_eq_map_deleteEdges {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    smoothAndCollapse G h₁ h₂ hne =
      (G.map (contractVertexMap u w)).deleteEdges {e₁, e₂} := by
  apply Graph.ext
  · simp only [Graph.vertexSet_deleteEdges, Graph.vertexSet_map]
    by_cases huw : u = w
    · subst w
      simp
    · rw [vertexSet_smoothAndCollapse_of_ne G h₁ h₂ hne huw]
      exact (image_contractVertexMap_of_ne h₁.left_mem huw).symm
  · intro f x y
    rw [isLink_smoothAndCollapse]
    simp only [Graph.deleteEdges_isLink, Graph.map_isLink, Relation.Map,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

/-- The compound smoothing operation is two legal split-off-minor steps: a
split followed by either a contraction or a loop deletion. -/
theorem smoothAndCollapse_isSplitOffMinor {α β : Type u} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    IsSplitOffMinor (smoothAndCollapse G h₁ h₂ hne) G := by
  classical
  unfold smoothAndCollapse
  split <;> rename_i huw
  · exact IsSplitOffMinor.trans
      (IsSplitOffMinor.deleteEdges (splitOff G h₁ h₂ hne) {e₁})
      (IsSplitOffMinor.split G h₁ h₂ hne)
  · exact IsSplitOffMinor.trans
      (IsSplitOffMinor.contract (splitOff G h₁ h₂ hne)
        (isLink_splitOff_new G h₁ h₂ hne) huw)
      (IsSplitOffMinor.split G h₁ h₂ hne)

/-- Smoothing and collapsing removes two live edge copies. -/
theorem ncard_edgeSet_smoothAndCollapse {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (smoothAndCollapse G h₁ h₂ hne).edgeSet.ncard =
      G.edgeSet.ncard - 2 := by
  rw [edgeSet_smoothAndCollapse, Set.ncard_sdiff]
  · simp [hne]
  · intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact h₁.edge_mem
    · exact h₂.edge_mem

/-- On a finite edge set, smoothing and collapsing strictly decreases the
number of live edges. -/
theorem ncard_edgeSet_smoothAndCollapse_lt {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) (hfinite : G.edgeSet.Finite) :
    (smoothAndCollapse G h₁ h₂ hne).edgeSet.ncard <
      G.edgeSet.ncard := by
  rw [edgeSet_smoothAndCollapse]
  have hsub : ({e₁, e₂} : Set β) ⊆ G.edgeSet := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · exact h₁.edge_mem
    · exact h₂.edge_mem
  have hpair : ({e₁, e₂} : Set β).ncard = 2 := by
    simp [hne]
  have hle : 2 ≤ G.edgeSet.ncard := by
    rw [← hpair]
    exact Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_sdiff hsub, hpair]
  omega

end StrongRoberson
