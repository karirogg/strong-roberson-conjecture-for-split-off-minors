import StrongRoberson.Basic

/-!
# Oddomorphisms

This file formalizes Definition 1 from `paper-source/main.tex`, lines 132--144.
The source is a multigraph and the target is simple. Parity is computed by
counting live edge copies, rather than neighboring vertices, so parallel edges
are counted with their correct multiplicity.
-/

namespace StrongRoberson

/-- The number of source edge copies incident with `u` whose other endpoint
maps to the target vertex `y`.

When `y` is adjacent to `φ u`, this is the degree of `u` in the inverse image
of the target edge with endpoints `φ u` and `y`.
-/
noncomputable def MultigraphHom.edgeFiberDegree
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) (u : F.vertexSet) (y : γ) : ℕ :=
  {e : F.edgeSet | ∃ v : F.vertexSet,
    F.IsLink e.1 u.1 v.1 ∧ φ v = y}.ncard

/-- An oddomorphism from a finite multigraph `F` to a simple graph `G`.

`oddVertices` is the paper's odd/even labelling. The final field is an
iff rather than two implications: its forward direction says odd vertices
have odd degree in every incident target-edge fibre, while its reverse
direction says even vertices have even degree.
-/
structure Oddomorphism {α β γ : Type*} (F : Graph α β) (G : SimpleGraph γ)
    [Finite F.vertexSet] [Finite F.edgeSet] extends MultigraphHom F G where
  oddVertices : Set F.vertexSet
  odd_fiber : ∀ y : γ,
    Odd {u : F.vertexSet | u ∈ oddVertices ∧ toFun u = y}.ncard
  degree_parity : ∀ (u : F.vertexSet) ⦃y : γ⦄,
    G.Adj (toFun u) y →
      (u ∈ oddVertices ↔
        Odd (MultigraphHom.edgeFiberDegree toMultigraphHom u y))

namespace Oddomorphism

instance {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet] :
    CoeFun (Oddomorphism F G) (fun _ ↦ F.vertexSet → γ) :=
  ⟨fun φ ↦ φ.toFun⟩

/-- The degree clause for vertices labelled even, derived from the iff in the
definition. -/
theorem edgeFiberDegree_even_iff_not_mem_oddVertices
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) (u : F.vertexSet) {y : γ}
    (huy : G.Adj (φ u) y) :
    Even (φ.toMultigraphHom.edgeFiberDegree u y) ↔
      u ∉ φ.oddVertices := by
  exact Nat.not_odd_iff_even.symm.trans
    (not_congr (φ.degree_parity u huy)).symm

end Oddomorphism

end StrongRoberson
