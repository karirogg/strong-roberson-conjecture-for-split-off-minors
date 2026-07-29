import StrongRoberson.Basic

/-!
# Split-off minors

This file formalizes the operations from `paper-source/main.tex`, lines
95--115, and the split-off-minor relation from lines 292--301.

All operations below are multigraph operations. In particular, contraction
keeps parallel edges and loops, and splitting off never simplifies its result.
-/

open Set
open scoped Sym2

namespace StrongRoberson

universe u

/-- Change the ends of an existing edge while preserving the vertex set, edge
set, and every other edge. This is an implementation primitive for
`splitOff`. -/
def reattachEdge {α β : Type*} (G : Graph α β) (e : β) (u v : α)
    (he : e ∈ G.edgeSet) (hu : u ∈ G.vertexSet) (hv : v ∈ G.vertexSet) :
    Graph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet
  IsLink f x y :=
    (f = e ∧ s(x, y) = s(u, v)) ∨ (f ≠ e ∧ G.IsLink f x y)
  isLink_symm := by
    intro f hf
    constructor
    intro x y hxy
    rcases hxy with hnew | hold
    · exact Or.inl ⟨hnew.1, Sym2.eq_swap.trans hnew.2⟩
    · exact Or.inr ⟨hold.1, hold.2.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro f x y z w hxy hzw
    rcases hxy with hxy | hxy <;> rcases hzw with hzw | hzw
    · have h : s(x, y) = s(z, w) := hxy.2.trans hzw.2.symm
      rw [Sym2.eq_iff] at h
      exact h.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
    · exact (hzw.1 hxy.1).elim
    · exact (hxy.1 hzw.1).elim
    · exact hxy.2.left_eq_or_eq hzw.2
  edge_mem_iff_exists_isLink := by
    intro f
    constructor
    · intro hf
      by_cases hfe : f = e
      · exact ⟨u, v, Or.inl ⟨hfe, rfl⟩⟩
      · obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet hf
        exact ⟨x, y, Or.inr ⟨hfe, hxy⟩⟩
    · rintro ⟨x, y, hnew | hold⟩
      · simpa only [hnew.1] using he
      · exact hold.2.edge_mem
  left_mem_of_isLink := by
    intro f x y hxy
    rcases hxy with hnew | hold
    · have h := hnew.2
      rw [Sym2.eq_iff] at h
      rcases h with h | h
      · simpa only [h.1] using hu
      · simpa only [h.1] using hv
    · exact hold.2.left_mem

@[simp]
theorem vertexSet_reattachEdge {α β : Type*} (G : Graph α β)
    (e : β) (u v : α) (he hu hv) :
    (reattachEdge G e u v he hu hv).vertexSet = G.vertexSet :=
  rfl

@[simp]
theorem edgeSet_reattachEdge {α β : Type*} (G : Graph α β)
    (e : β) (u v : α) (he hu hv) :
    (reattachEdge G e u v he hu hv).edgeSet = G.edgeSet :=
  rfl

/-- Contract a non-loop edge, retaining `u` as the representative of the
merged vertex.

Mapping first preserves every edge identity and turns the other edges between
`u` and `v` into loops. Deleting exactly `e` then agrees with the paper's
multigraph contraction formula, up to the name of the merged vertex.
-/
noncomputable def contractEdge {α β : Type*} (G : Graph α β)
    {e : β} {u v : α} (_ : G.IsLink e u v) (_ : u ≠ v) : Graph α β := by
  classical
  exact (G.map (Function.update id v u)).deleteEdges {e}

@[simp]
theorem edgeSet_contractEdge {α β : Type*} (G : Graph α β)
    {e : β} {u v : α} (he : G.IsLink e u v) (hne : u ≠ v) :
    (contractEdge G he hne).edgeSet = G.edgeSet \ {e} :=
  rfl

/-- Split off the distinct edge copies `e₁ = uv` and `e₂ = vw`.

The result deletes `e₂` and reuses the identity `e₁` for the new edge `uw`;
thus both old edge copies disappear and exactly one new edge copy is created.
Endpoint coincidences are allowed, so `u = w` creates a loop.
-/
def splitOff {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) : Graph α β :=
  reattachEdge (G.deleteEdges {e₂}) e₁ u w
    (by
      simp only [Graph.edgeSet_deleteEdges, Set.mem_sdiff, h₁.edge_mem,
        Set.mem_singleton_iff, hne, not_false_eq_true, and_self])
    (by
      simpa only [Graph.vertexSet_deleteEdges] using h₁.left_mem)
    (by
      simpa only [Graph.vertexSet_deleteEdges] using h₂.right_mem)

@[simp]
theorem vertexSet_splitOff {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (splitOff G h₁ h₂ hne).vertexSet = G.vertexSet :=
  rfl

@[simp]
theorem edgeSet_splitOff {α β : Type*} (G : Graph α β)
    {e₁ e₂ : β} {u v w : α}
    (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
    (hne : e₁ ≠ e₂) :
    (splitOff G h₁ h₂ hne).edgeSet = G.edgeSet \ {e₂} :=
  rfl

/-- `IsSplitOffMinor H G` means that `H` can be obtained from `G` by a finite
sequence of multigraph subgraph, non-loop contraction, and split-off
operations, with harmless relabelling by multigraph isomorphisms.

The heterogeneous indices are intentional: contraction and a final comparison
with a separately presented graph need not use the same vertex or edge types.
-/
inductive IsSplitOffMinor :
    {α β : Type u} → Graph α β →
    {γ δ : Type u} → Graph γ δ → Prop where
  | refl {α β : Type u} (G : Graph α β) :
      IsSplitOffMinor G G
  | iso {α β γ δ : Type u} {H : Graph α β} {G : Graph γ δ}
      (i : GraphIso H G) :
      IsSplitOffMinor H G
  | subgraph {α β : Type u} {H G : Graph α β} (h : H ≤ G) :
      IsSplitOffMinor H G
  | contract {α β : Type u} (G : Graph α β)
      {e : β} {u v : α} (he : G.IsLink e u v) (hne : u ≠ v) :
      IsSplitOffMinor (contractEdge G he hne) G
  | split {α β : Type u} (G : Graph α β)
      {e₁ e₂ : β} {u v w : α}
      (h₁ : G.IsLink e₁ u v) (h₂ : G.IsLink e₂ v w)
      (hne : e₁ ≠ e₂) :
      IsSplitOffMinor (splitOff G h₁ h₂ hne) G
  | trans {α β γ δ ε ζ : Type u}
      {H : Graph α β} {K : Graph γ δ} {G : Graph ε ζ} :
      IsSplitOffMinor H K → IsSplitOffMinor K G → IsSplitOffMinor H G

end StrongRoberson
