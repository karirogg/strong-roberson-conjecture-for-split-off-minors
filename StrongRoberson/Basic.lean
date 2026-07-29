import Mathlib

/-!
# Multigraph foundations

The paper works with finite simple graphs at its endpoints, but the definition
of a split-off minor explicitly permits multigraphs in intermediate steps.
Consequently, this development uses Mathlib's edge-typed `Graph` for
multigraphs and `SimpleGraph` only where simplicity is part of the statement.

This file supplies the small amount of infrastructure that is not yet present
in Mathlib's new multigraph API:

* conversion of a simple graph to an edge-typed multigraph;
* vertex homomorphisms from multigraphs to simple graphs; and
* multigraph isomorphisms that may change the vertex and edge types.
-/

open Set
open scoped Sym2

namespace StrongRoberson

universe u

/-- A simple graph regarded as a multigraph.

Each edge keeps its unordered pair of endpoints as its edge identity. All
vertices of the ambient type, including isolated vertices, are retained.
-/
def simpleToMultiGraph {α : Type*} (G : SimpleGraph α) : Graph α (Sym2 α) where
  vertexSet := Set.univ
  edgeSet := G.edgeSet
  IsLink e x y := e = s(x, y) ∧ G.Adj x y
  isLink_symm := fun _ _ =>
    { symm _ _ hxy := ⟨hxy.1.trans Sym2.eq_swap, hxy.2.symm⟩ }
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w hxy hvw
    have h := hxy.1.symm.trans hvw.1
    rw [Sym2.eq_iff] at h
    exact h.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  edge_mem_iff_exists_isLink := by
    intro e
    refine Sym2.inductionOn e ?_
    intro x y
    constructor
    · intro hxy
      rw [G.mem_edgeSet] at hxy
      exact ⟨x, y, rfl, hxy⟩
    · rintro ⟨u, v, huv, hadj⟩
      rw [huv, G.mem_edgeSet]
      exact hadj
  left_mem_of_isLink := by
    simp only [Set.mem_univ, implies_true]

@[simp]
theorem vertexSet_simpleToMultiGraph {α : Type*} (G : SimpleGraph α) :
    (simpleToMultiGraph G).vertexSet = Set.univ :=
  rfl

@[simp]
theorem edgeSet_simpleToMultiGraph {α : Type*} (G : SimpleGraph α) :
    (simpleToMultiGraph G).edgeSet = G.edgeSet :=
  rfl

@[simp]
theorem isLink_simpleToMultiGraph {α : Type*} (G : SimpleGraph α)
    (e : Sym2 α) (x y : α) :
    (simpleToMultiGraph G).IsLink e x y ↔ e = s(x, y) ∧ G.Adj x y :=
  Iff.rfl

/-- A vertex homomorphism from a multigraph to a simple graph.

The map is defined only on the live vertex subtype of the multigraph. Edge
copies are not mapped separately: their target edge is determined uniquely by
the images of their endpoints because the target is simple.
-/
structure MultigraphHom {α β γ : Type*} (F : Graph α β) (G : SimpleGraph γ) where
  toFun : F.vertexSet → γ
  map_isLink : ∀ ⦃e u v⦄ (h : F.IsLink e u v),
    G.Adj (toFun ⟨u, h.left_mem⟩) (toFun ⟨v, h.right_mem⟩)

namespace MultigraphHom

instance {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ} :
    CoeFun (MultigraphHom F G) (fun _ ↦ F.vertexSet → γ) :=
  ⟨toFun⟩

/-- Regard an ordinary simple-graph homomorphism as a homomorphism out of the
corresponding multigraph. -/
def ofSimpleGraph {α γ : Type*} {F : SimpleGraph α} {G : SimpleGraph γ}
    (φ : F →g G) : MultigraphHom (simpleToMultiGraph F) G where
  toFun x := φ x
  map_isLink := by
    intro e u v h
    exact φ.map_adj h.2

end MultigraphHom

/-- An isomorphism of multigraphs, allowing both the vertex and edge types to
change. Only live vertices and live edge copies are related.

The explicit edge equivalence is essential: parallel edges have distinct
identities even when they have the same endpoints.
-/
structure GraphIso {α β γ δ : Type u} (F : Graph α β) (G : Graph γ δ) where
  vertexEquiv : F.vertexSet ≃ G.vertexSet
  edgeEquiv : F.edgeSet ≃ G.edgeSet
  map_isLink : ∀ (e : F.edgeSet) (x y : F.vertexSet),
    F.IsLink e.1 x.1 y.1 ↔
      G.IsLink (edgeEquiv e).1 (vertexEquiv x).1 (vertexEquiv y).1

namespace GraphIso

/-- The identity multigraph isomorphism. -/
def refl {α β : Type u} (F : Graph α β) : GraphIso F F where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  map_isLink := by
    simp only [Equiv.refl_apply, implies_true]

/-- Reverse a multigraph isomorphism. -/
def symm {α β γ δ : Type u} {F : Graph α β} {G : Graph γ δ}
    (i : GraphIso F G) : GraphIso G F where
  vertexEquiv := i.vertexEquiv.symm
  edgeEquiv := i.edgeEquiv.symm
  map_isLink e x y := by
    simpa only [Equiv.apply_symm_apply] using
      (i.map_isLink (i.edgeEquiv.symm e)
      (i.vertexEquiv.symm x) (i.vertexEquiv.symm y)).symm

/-- Compose multigraph isomorphisms. -/
def trans {α β γ δ ε ζ : Type u}
    {F : Graph α β} {G : Graph γ δ} {H : Graph ε ζ}
    (i : GraphIso F G) (j : GraphIso G H) : GraphIso F H where
  vertexEquiv := i.vertexEquiv.trans j.vertexEquiv
  edgeEquiv := i.edgeEquiv.trans j.edgeEquiv
  map_isLink e x y := (i.map_isLink e x y).trans
    (j.map_isLink (i.edgeEquiv e) (i.vertexEquiv x) (i.vertexEquiv y))

end GraphIso

end StrongRoberson
