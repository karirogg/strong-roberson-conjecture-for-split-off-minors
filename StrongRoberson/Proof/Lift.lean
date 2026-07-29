import StrongRoberson.Proof.ChordWalk
import StrongRoberson.Proof.LiftAssembly

/-!
# The perfect-fibre (lift) case

This file formalizes the first lemma in Section 4 of the paper: a lift of the
target graph contains the target as a split-off minor.  We use the paper's
equivalent local description of a lift: over every target edge, every source
vertex is incident with exactly one edge copy going to the opposite fibre.
-/

namespace StrongRoberson

universe u

namespace Oddomorphism

/-- Condition (i) of an oddomorphism makes its vertex map surjective, including
at isolated target vertices. -/
theorem surjective
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : Oddomorphism F G) :
    Function.Surjective φ := by
  intro y
  have hpos :
      0 < {u : F.vertexSet | u ∈ φ.oddVertices ∧ φ u = y}.ncard :=
    (φ.odd_fiber y).pos
  obtain ⟨u, hu⟩ :=
    (Set.ncard_pos
      (s := {u : F.vertexSet | u ∈ φ.oddVertices ∧ φ u = y})).mp hpos
  exact ⟨u, hu.2⟩

end Oddomorphism

/-- Paper Lemma `perfect-matching-lm`: a surjective multigraph homomorphism
whose target-edge preimages are perfect matchings exhibits the target as a
split-off minor of the source.

The formal proof follows the paper's spanning-forest construction. -/
theorem perfectFibers_implies_splitOffMinor
    {α β γ : Type u} [Finite α] [Finite β] [Finite γ]
    (F : Graph α β) (G : SimpleGraph γ)
    (φ : MultigraphHom F G)
    (hφ : φ.HasPerfectFibers) :
    IsSplitOffMinor (simpleToMultiGraph G) F := by
  apply
    MultigraphHom.Covering.perfectFibers_implies_splitOffMinor_of_chordBoundaryProvider
      φ hφ
  intro c x y hxy hnotT
  exact MultigraphHom.Covering.chordBoundaryCertificate
    φ hφ (FullSpanningForest.choose G) c x y hxy hnotT

end StrongRoberson
