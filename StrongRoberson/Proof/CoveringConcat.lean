import StrongRoberson.Proof.CoveringOrbit

/-!
# Composition of transport in a quiver covering

The endpoint indices of a lifted path are definitionally source vertices but
only propositionally the corresponding target vertices.  This file packages
the resulting casts once, proving that unique path transport and the lifted
source paths respect concatenation.
-/

namespace Quiver.Path

universe u

/-- Composition preserves heterogeneous equality when the three endpoint
equalities are supplied explicitly. -/
theorem comp_heq_of_eq
    {U : Type u} [Quiver U]
    {a b c a' b' c' : U}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (p : Path a b) (q : Path b c)
    (p' : Path a' b') (q' : Path b' c')
    (hp : p ≍ p') (hq : q ≍ q') :
    p.comp q ≍ p'.comp q' := by
  subst a'
  subst b'
  subst c'
  have hp' : p = p' := eq_of_heq hp
  have hq' : q = q' := eq_of_heq hq
  subst p'
  subst q'
  rfl

end Quiver.Path

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- The path component of the unique lift used by `pathTransport`. -/
noncomputable def transportedPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) :
    Quiver.Path u.1 (pathTransport φ hφ p u).1 :=
  (liftPath φ hφ u.1 (targetPathAt φ p u)).2

/-- Concatenating two endpoint-cast target paths gives the cast of their
concatenation, up to heterogeneous equality. -/
theorem targetPathAt_comp_heq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) {x y z : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (q : Quiver.Path (show Target G from y) (show Target G from z))
    (u : Fiber φ x) (v : Fiber φ y) :
    (targetPathAt φ p u).comp
        ((targetPathAt φ q v).cast v.2 rfl) ≍
      targetPathAt φ (p.comp q) u := by
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  dsimp [targetPathAt] at *
  subst x
  subst y
  rfl

/-- The lift of a concatenated target path is the concatenation of its two
successive unique lifts, packaged as an equality of path-stars. -/
theorem liftPath_comp
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y z : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (q : Quiver.Path (show Target G from y) (show Target G from z))
    (u : Fiber φ x) :
    liftPath φ hφ u.1 (targetPathAt φ (p.comp q) u) =
      ⟨(pathTransport φ hφ q (pathTransport φ hφ p u)).1,
        (transportedPath φ hφ p u).comp
          (transportedPath φ hφ q
            (pathTransport φ hφ p u))⟩ := by
  let v := pathTransport φ hφ p u
  let w := pathTransport φ hφ q v
  let r : Quiver.PathStar u.1 :=
    ⟨w.1, (transportedPath φ hφ p u).comp
      (transportedPath φ hφ q v)⟩
  have hvT :
      (show Target G from φ v.1) =
        (show Target G from y) :=
    v.2
  have hwT :
      (show Target G from φ w.1) =
        (show Target G from z) :=
    w.2
  have hr :
      (toPrefunctor φ).pathStar u.1 r =
        ⟨(show Target G from z),
          targetPathAt φ (p.comp q) u⟩ := by
    refine Sigma.ext hwT ?_
    change
      (toPrefunctor φ).mapPath
          ((transportedPath φ hφ p u).comp
            (transportedPath φ hφ q v)) ≍
        targetPathAt φ (p.comp q) u
    rw [Prefunctor.mapPath_comp]
    have hp :=
      map_liftPath_path φ hφ u.1
        (targetPathAt φ p u)
    have hq :=
      map_liftPath_path φ hφ v.1
        (targetPathAt φ q v)
    have hqcast :
        (toPrefunctor φ).mapPath
            (transportedPath φ hφ q v) ≍
          (targetPathAt φ q v).cast hvT rfl :=
      hq.trans (Quiver.Path.cast_heq hvT rfl _).symm
    exact
      (Quiver.Path.comp_heq_of_eq (U := Target G)
        rfl hvT hwT
        ((toPrefunctor φ).mapPath
          (transportedPath φ hφ p u))
        ((toPrefunctor φ).mapPath
          (transportedPath φ hφ q v))
        (targetPathAt φ p u)
        ((targetPathAt φ q v).cast hvT rfl)
        hp hqcast).trans
          (targetPathAt_comp_heq φ p q u v)
  change
    liftPathStar φ hφ u.1
        ⟨(show Target G from z),
          targetPathAt φ (p.comp q) u⟩ = r
  rw [← hr]
  exact liftPathStar_map φ hφ u.1 r

/-- Endpoint transport respects target-path concatenation. -/
@[simp]
theorem pathTransport_comp
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y z : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (q : Quiver.Path (show Target G from y) (show Target G from z))
    (u : Fiber φ x) :
    pathTransport φ hφ (p.comp q) u =
      pathTransport φ hφ q (pathTransport φ hφ p u) := by
  apply Subtype.ext
  exact congrArg Sigma.fst (liftPath_comp φ hφ p q u)

/-- The lifted source path of a target concatenation is heterogeneously equal
to the concatenation of the two successive lifted source paths. -/
theorem transportedPath_comp
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y z : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (q : Quiver.Path (show Target G from y) (show Target G from z))
    (u : Fiber φ x) :
    transportedPath φ hφ (p.comp q) u ≍
      (transportedPath φ hφ p u).comp
        (transportedPath φ hφ q
          (pathTransport φ hφ p u)) :=
  (Sigma.mk.inj_iff.mp (liftPath_comp φ hφ p q u)).2

end MultigraphHom.Covering

end StrongRoberson
