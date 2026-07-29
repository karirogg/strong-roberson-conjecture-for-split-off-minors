import StrongRoberson.Proof.CoveringConcat

/-!
# Reversing a lifted path

This acyclic covering-layer module proves that unique path lifting commutes
with reversal.  It deliberately does not import the lifted-forest or outside
path layers.
-/

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- Equal source-fibre points determine heterogeneously equal lifted path
components. -/
theorem transportedPath_heq_of_fiber_eq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    {u v : Fiber φ x} (huv : u = v) :
    transportedPath φ hφ p u ≍
      transportedPath φ hφ p v := by
  subst v
  rfl

/-- Reversing a target path and lifting from the transported endpoint gives
the reverse of the original lifted source path. -/
theorem transportedPath_reverse
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) :
    transportedPath φ hφ p.reverse
        (pathTransport φ hφ p u) ≍
      (transportedPath φ hφ p u).reverse := by
  let q := liftPath φ hφ u.1 (targetPathAt φ p u)
  let v : Fiber φ y :=
    ⟨q.1, liftPath_endpoint φ hφ u.1
      (targetPathAt φ p u)⟩
  have hv : v = pathTransport φ hφ p u := rfl
  have hmaprev :
      (toPrefunctor φ).pathStar q.1
          (PathStar.reverse q) =
        ⟨(show Target G from x),
          targetPathAt φ p.reverse v⟩ := by
    rw [pathStar_reverse]
    refine Sigma.ext u.2 ?_
    exact
      (Path.reverse_heq_of_eq (U := Target G) rfl
        (liftPath_endpoint φ hφ u.1
          (targetPathAt φ p u))
        (map_liftPath_path φ hφ u.1
          (targetPathAt φ p u))).trans
        (targetPathAt_reverse_heq φ p u v)
  have hlift :
      liftPathStar φ hφ q.1
          ⟨(show Target G from x),
            targetPathAt φ p.reverse v⟩ =
        PathStar.reverse q := by
    rw [← hmaprev]
    exact liftPathStar_map φ hφ q.1
      (PathStar.reverse q)
  have hpathV :
      transportedPath φ hφ p.reverse v ≍
        (transportedPath φ hφ p u).reverse :=
    (Sigma.mk.inj_iff.mp hlift).2
  exact
    (transportedPath_heq_of_fiber_eq
      φ hφ p.reverse hv.symm).trans hpathV

end MultigraphHom.Covering

end StrongRoberson
