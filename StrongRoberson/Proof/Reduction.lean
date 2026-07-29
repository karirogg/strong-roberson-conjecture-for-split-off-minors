import StrongRoberson.Proof.Lift
import StrongRoberson.Proof.FiberReduction

/-!
# Parity reduction of an oddomorphism

This file formalizes the iterative construction `F ↦ F'' ↦ F₁` in the proof
of Theorem 6:

* delete edge-disjoint circuits inside each target-edge preimage;
* split off the remaining maximal trails;
* delete the newly isolated even vertices;
* contract the edges that now lie inside a single target-vertex fibre; and
* repeat until every target-edge preimage is a perfect matching.

The paper batches the smoothing operations into trails and circuits.  The
formal reduction uses the equivalent local formulation proved in
`FiberReduction`: whenever a coloured fibre degree exceeds one, choose two
edge copies at that vertex, smooth them, and immediately collapse the new
monochromatic edge.  Each local move preserves the parity state and removes
two live edge copies.  At termination, `Terminal` deletes the isolated
weight-zero vertices.

The output types remain existential because the public reduction certificate
is designed to accommodate later heterogeneous variants of the construction.
-/

namespace StrongRoberson

universe u

/-- The output certificate of the paper's terminating parity reduction. -/
structure PerfectFiberReduction
    {α β γ : Type u} (F : Graph α β) (G : SimpleGraph γ) where
  vertexType : Type u
  edgeType : Type u
  finite_vertexType : Finite vertexType
  finite_edgeType : Finite edgeType
  graph : Graph vertexType edgeType
  hom : MultigraphHom graph G
  perfect : hom.HasPerfectFibers
  isSplitOffMinor : IsSplitOffMinor graph F

attribute [instance]
  PerfectFiberReduction.finite_vertexType
  PerfectFiberReduction.finite_edgeType

namespace Oddomorphism

/-- Extend an oddomorphism's colouring from the live vertex subtype to the
ambient vertex type.  The value away from the live vertices is immaterial to
all graph and parity conditions. -/
noncomputable def ambientColor
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet] [Nonempty γ]
    (φ : Oddomorphism F G) : α → γ := by
  classical
  intro x
  exact if hx : x ∈ F.vertexSet then
    φ ⟨x, hx⟩
  else
    Classical.choice inferInstance

/-- The preceding ambient colouring agrees with the original oddomorphism on
every live vertex. -/
theorem ambientColor_isAmbientExtension
    {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet] [Nonempty γ]
    (φ : Oddomorphism F G) :
    φ.toMultigraphHom.IsAmbientExtension φ.ambientColor := by
  intro x hx
  simp [ambientColor, hx]

end Oddomorphism

/-- Iterating the preceding reduction terminates with perfect target-edge
fibres, and every step is a split-off-minor operation. -/
noncomputable def oddomorphism_has_perfectFiberReduction
    {α β γ : Type u} [Finite α] [Finite β] [Finite γ]
    (F : Graph α β) (G : SimpleGraph γ)
    (φ : Oddomorphism F G) :
    PerfectFiberReduction F G := by
  classical
  by_cases hγ : Nonempty γ
  · letI : Nonempty γ := hγ
    let color : α → γ := φ.ambientColor
    let S : WeightedParityState F G color :=
      φ.toWeightedParityState color φ.ambientColor_isAmbientExtension
    let R := WeightedParityState.normalizeFiberDegrees F S
    exact
      { vertexType := α
        edgeType := β
        finite_vertexType := inferInstance
        finite_edgeType := inferInstance
        graph := R.state.positiveGraph
        hom := R.state.positiveHom R.reduced
        perfect := R.state.positiveHom_hasPerfectFibers R.reduced
        isSplitOffMinor :=
          (R.state.positiveGraph_isSplitOffMinor).trans
            R.isSplitOffMinor }
  · letI : IsEmpty γ := ⟨fun y ↦ hγ ⟨y⟩⟩
    exact
      { vertexType := α
        edgeType := β
        finite_vertexType := inferInstance
        finite_edgeType := inferInstance
        graph := F
        hom := φ.toMultigraphHom
        perfect := by
          constructor
          · intro y
            exact isEmptyElim y
          · intro x
            exact isEmptyElim (φ x)
        isSplitOffMinor := .refl F }

end StrongRoberson
