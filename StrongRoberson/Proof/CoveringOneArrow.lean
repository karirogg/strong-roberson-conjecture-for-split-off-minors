import StrongRoberson.Proof.CoveringConcat

/-!
# Canonical lifting of one target arrow

The perfect-fibre hypothesis identifies every source star with its target
star.  This file names the inverse image of a target star and relates it
directly to the general path-transport construction applied to a one-arrow
path.
-/

namespace Quiver.Hom

/-- Turning arrows into one-arrow paths respects heterogeneous equality when
their endpoint equalities are supplied explicitly. -/
theorem toPath_heq_of_eq
    {V : Type*} [Quiver V] {a b a' b' : V}
    (ha : a = a') (hb : b = b')
    (e : a ⟶ b) (e' : a' ⟶ b') (hee' : e ≍ e') :
    e.toPath ≍ e'.toPath := by
  subst a'
  subst b'
  have hee' : e = e' := eq_of_heq hee'
  subst e'
  rfl

end Quiver.Hom

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- The star equivalence induced by a perfect-fibre multigraph homomorphism. -/
noncomputable def sourceStarEquiv
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) :
    Quiver.Star u ≃ Quiver.Star ((toPrefunctor φ).obj u) :=
  Equiv.ofBijective _ (star_bijective φ hφ u)

/-- The canonical source star above a target star, obtained by applying the
inverse of `sourceStarEquiv`. -/
noncomputable def liftStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (h : Quiver.Star ((toPrefunctor φ).obj u)) :
    Quiver.Star u :=
  (sourceStarEquiv φ hφ u).symm h

/-- Mapping the canonical lifted star recovers the target star. -/
@[simp]
theorem map_liftStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (h : Quiver.Star ((toPrefunctor φ).obj u)) :
    (toPrefunctor φ).star u (liftStar φ hφ u h) = h :=
  (sourceStarEquiv φ hφ u).apply_symm_apply h

/-- Lifting the one-arrow target path as a path-star gives the one-arrow path
of the canonical inverse-star lift. -/
theorem liftPath_toPath_eq_liftStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (h : Quiver.Star ((toPrefunctor φ).obj u)) :
    liftPath φ hφ u
        (targetPathAt φ h.2.toPath
          (show Fiber φ (φ u) from ⟨u, rfl⟩)) =
      ⟨(liftStar φ hφ u h).1,
        (liftStar φ hφ u h).2.toPath⟩ := by
  apply (pathStar_bijective φ hφ u).1
  rw [map_liftPath]
  have hs := map_liftStar φ hφ u h
  have hs_fst :
      (toPrefunctor φ).obj (liftStar φ hφ u h).1 = h.1 :=
    congrArg Sigma.fst hs
  have hs_snd :
      (toPrefunctor φ).map (liftStar φ hφ u h).2 ≍ h.2 :=
    (Sigma.mk.inj_iff.mp hs).2
  refine Sigma.ext hs_fst.symm ?_
  simpa [targetPathAt] using
    Quiver.Hom.toPath_heq_of_eq rfl hs_fst.symm
      h.2
      ((toPrefunctor φ).map (liftStar φ hφ u h).2)
      hs_snd.symm

/-- The endpoint computed by one-arrow path transport is the endpoint of the
canonical lifted source star. -/
@[simp]
theorem pathTransport_toPath_eq_liftStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (h : Quiver.Star ((toPrefunctor φ).obj u)) :
    (pathTransport φ hφ h.2.toPath
      (show Fiber φ (φ u) from ⟨u, rfl⟩)).1 =
        (liftStar φ hφ u h).1 := by
  exact congrArg Sigma.fst
    (liftPath_toPath_eq_liftStar φ hφ u h)

/-- The path computed by one-arrow path transport is the chosen lifted source
arrow, regarded as a one-arrow path. -/
theorem transportedPath_toPath_heq_liftStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (h : Quiver.Star ((toPrefunctor φ).obj u)) :
    transportedPath φ hφ h.2.toPath
        (show Fiber φ (φ u) from ⟨u, rfl⟩) ≍
      (liftStar φ hφ u h).2.toPath :=
  (Sigma.mk.inj_iff.mp
    (liftPath_toPath_eq_liftStar φ hφ u h)).2

end MultigraphHom.Covering

end StrongRoberson
