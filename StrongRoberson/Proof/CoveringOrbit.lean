import StrongRoberson.Proof.Covering
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Path transport and finite covering orbits

A path in the target of a quiver covering transports a source vertex in the
fibre over its initial endpoint to the endpoint of its unique lift.  Reversing
the target path reverses this transport, so the transport is an equivalence of
source vertex fibres.

For a closed target path this gives a permutation of one finite fibre.  The
second part of the file packages its least positive return time.
-/

namespace StrongRoberson

namespace MultigraphHom.Covering

/-! ## Reversal of path-stars -/

/-- Reverse the path component of a path-star. -/
def PathStar.reverse
    {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {u : V} (p : Quiver.PathStar u) : Quiver.PathStar p.1 :=
  ⟨u, p.2.reverse⟩

@[simp]
theorem PathStar.reverse_fst
    {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {u : V} (p : Quiver.PathStar u) :
    (PathStar.reverse p).1 = u :=
  rfl

@[simp]
theorem PathStar.reverse_reverse
    {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {u : V} (p : Quiver.PathStar u) :
    PathStar.reverse (PathStar.reverse p) = p := by
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    exact p.2.reverse_reverse

/-- A reversal-preserving prefunctor commutes with path reversal. -/
theorem mapPath_reverse
    {U V : Type*} [Quiver U] [Quiver V]
    [Quiver.HasReverse U] [Quiver.HasReverse V]
    (ψ : U ⥤q V) [ψ.MapReverse]
    {u v : U} (p : Quiver.Path u v) :
    ψ.mapPath p.reverse = (ψ.mapPath p).reverse := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change
        ψ.mapPath ((Quiver.reverse e).toPath.comp p.reverse) =
          (Quiver.reverse (ψ.map e)).toPath.comp
            (ψ.mapPath p).reverse
      rw [Prefunctor.mapPath_comp, Prefunctor.mapPath_toPath,
        Prefunctor.map_reverse, ih]

/-- Path-star mapping commutes with reversal. -/
@[simp]
theorem pathStar_reverse
    {U V : Type*} [Quiver U] [Quiver V]
    [Quiver.HasReverse U] [Quiver.HasReverse V]
    (ψ : U ⥤q V) [ψ.MapReverse]
    {u : U} (p : Quiver.PathStar u) :
    ψ.pathStar p.1 (PathStar.reverse p) =
      PathStar.reverse (ψ.pathStar u p) := by
  refine Sigma.ext ?_ ?_
  · rfl
  · apply heq_of_eq
    exact mapPath_reverse ψ p.2

/-! ## Transport along a fixed target path -/

/-- The source vertex fibre of a multigraph homomorphism over `x`. -/
def Fiber
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) (x : γ) :=
  {u : F.vertexSet // φ u = x}

/-- Regard a path starting at `x` as a path starting at the image of a
specified source vertex over `x`. -/
def targetPathAt
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) :
    Quiver.Path ((toPrefunctor φ).obj u.1) (show Target G from y) :=
  Quiver.Path.cast u.2.symm rfl p

/-- `targetPathAt` only changes the endpoint indices of the given path. -/
theorem targetPathAt_heq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) :
    targetPathAt φ p u ≍ p :=
  Quiver.Path.cast_heq (U := Target G) u.2.symm rfl p

/-- Path reversal respects heterogeneous equality once the endpoint
equalities are made explicit. -/
theorem Path.reverse_heq_of_eq
    {U : Type*} [Quiver U] [Quiver.HasReverse U]
    {a b c d : U} {p : Quiver.Path a b} {q : Quiver.Path c d}
    (ha : a = c) (hb : b = d) (h : p ≍ q) :
    p.reverse ≍ q.reverse := by
  subst c
  subst d
  have hpq : p = q := eq_of_heq h
  subst q
  rfl

/-- Reversing a path indexed at one source fibre gives, up to the necessary
endpoint casts, the reverse path indexed at the other source fibre. -/
theorem targetPathAt_reverse_heq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) (v : Fiber φ y) :
    (targetPathAt φ p u).reverse ≍
      targetPathAt φ p.reverse v := by
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  dsimp [targetPathAt] at *
  subst x
  subst y
  rfl

/-- Endpoint transport obtained by uniquely lifting the fixed target path. -/
noncomputable def pathTransport
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y)) :
    Fiber φ x → Fiber φ y := fun u ↦
  ⟨(liftPath φ hφ u.1 (targetPathAt φ p u)).1,
    liftPath_endpoint φ hφ u.1 (targetPathAt φ p u)⟩

@[simp]
theorem pathTransport_map
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) :
    φ (pathTransport φ hφ p u).1 = y :=
  (pathTransport φ hφ p u).2

theorem pathTransport_reverse_apply
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) :
    pathTransport φ hφ p.reverse (pathTransport φ hφ p u) = u := by
  let q := liftPath φ hφ u.1 (targetPathAt φ p u)
  let v : Fiber φ y :=
    ⟨q.1, liftPath_endpoint φ hφ u.1 (targetPathAt φ p u)⟩
  have hv : v = pathTransport φ hφ p u := rfl
  have hmaprev :
      (toPrefunctor φ).pathStar q.1 (PathStar.reverse q) =
        ⟨(show Target G from x), targetPathAt φ p.reverse v⟩ := by
    rw [pathStar_reverse]
    refine Sigma.ext u.2 ?_
    exact
      (Path.reverse_heq_of_eq (U := Target G) rfl
        (liftPath_endpoint φ hφ u.1 (targetPathAt φ p u))
        (map_liftPath_path φ hφ u.1
          (targetPathAt φ p u))).trans
        (targetPathAt_reverse_heq φ p u v)
  have hlift :
      liftPathStar φ hφ q.1
          ⟨(show Target G from x), targetPathAt φ p.reverse v⟩ =
        PathStar.reverse q := by
    rw [← hmaprev]
    exact liftPathStar_map φ hφ q.1 (PathStar.reverse q)
  apply Subtype.ext
  rw [← hv]
  change
    (liftPathStar φ hφ v.1
      ⟨(show Target G from x), targetPathAt φ p.reverse v⟩).1 = u.1
  simpa [v, q, PathStar.reverse] using congr_arg Sigma.fst hlift

/-- Transport along a target path is an equivalence between its endpoint
source fibres.  Its inverse is transport along the reversed path. -/
noncomputable def pathTransportEquiv
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y)) :
    Fiber φ x ≃ Fiber φ y where
  toFun := pathTransport φ hφ p
  invFun := pathTransport φ hφ p.reverse
  left_inv := pathTransport_reverse_apply φ hφ p
  right_inv := by
    intro v
    simpa only [Quiver.Path.reverse_reverse] using
      pathTransport_reverse_apply φ hφ p.reverse v

@[simp]
theorem pathTransportEquiv_apply
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (u : Fiber φ x) :
    pathTransportEquiv φ hφ p u = pathTransport φ hφ p u :=
  rfl

@[simp]
theorem pathTransportEquiv_symm_apply
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from y))
    (v : Fiber φ y) :
    (pathTransportEquiv φ hφ p).symm v =
      pathTransport φ hφ p.reverse v :=
  rfl

/-- A closed target path acts as a permutation of its source vertex fibre. -/
noncomputable def pathPermutation
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from x)) :
    Equiv.Perm (Fiber φ x) :=
  pathTransportEquiv φ hφ p

/-! ## Minimal returns in finite permutation orbits -/

/-- The least positive return time of `a` under a permutation of a finite
type. -/
noncomputable def minimalReturnTime
    {δ : Type*} [Finite δ] (σ : Equiv.Perm δ) (a : δ) : ℕ :=
  Function.minimalPeriod σ a

/-- A permutation of a finite type always has a positive least return time. -/
theorem minimalReturnTime_pos
    {δ : Type*} [Finite δ] (σ : Equiv.Perm δ) (a : δ) :
    0 < minimalReturnTime σ a :=
  Function.minimalPeriod_pos_of_mem_periodicPts
    (σ.injective.mem_periodicPts a)

/-- Iterating through the least return time returns to the starting point. -/
@[simp]
theorem iterate_minimalReturnTime
    {δ : Type*} [Finite δ] (σ : Equiv.Perm δ) (a : δ) :
    (σ : δ → δ)^[minimalReturnTime σ a] a = a :=
  Function.iterate_minimalPeriod

/-- No positive time strictly before the least return time returns to the
starting point. -/
theorem iterate_ne_of_pos_lt_minimalReturnTime
    {δ : Type*} [Finite δ] (σ : Equiv.Perm δ) (a : δ)
    {k : ℕ} (hk : 0 < k) (hlt : k < minimalReturnTime σ a) :
    (σ : δ → δ)^[k] a ≠ a :=
  Function.not_isPeriodicPt_of_pos_of_lt_minimalPeriod hk.ne' hlt

/-- Before the least return time, all points of the orbit are distinct. -/
theorem iterate_injOn_Iio_minimalReturnTime
    {δ : Type*} [Finite δ] (σ : Equiv.Perm δ) (a : δ) :
    Set.InjOn (fun k : ℕ ↦ (σ : δ → δ)^[k] a)
      (Set.Iio (minimalReturnTime σ a)) := by
  exact Function.iterate_injOn_Iio_minimalPeriod

/-- Existential package of a positive minimal return, convenient when the
actual `minimalReturnTime` definition should remain hidden. -/
theorem exists_minimal_positive_return
    {δ : Type*} [Finite δ] (σ : Equiv.Perm δ) (a : δ) :
    ∃ n : ℕ, 0 < n ∧
      (σ : δ → δ)^[n] a = a ∧
      (∀ k : ℕ, 0 < k → k < n →
        (σ : δ → δ)^[k] a ≠ a) := by
  exact
    ⟨minimalReturnTime σ a, minimalReturnTime_pos σ a,
      iterate_minimalReturnTime σ a,
      fun _ hk hlt ↦
        iterate_ne_of_pos_lt_minimalReturnTime σ a hk hlt⟩

/-- Specialization of the finite-orbit return theorem to the monodromy
permutation induced by a closed target path. -/
theorem pathPermutation_exists_minimal_positive_return
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from x))
    (u : Fiber φ x) :
    ∃ n : ℕ, 0 < n ∧
      ((pathPermutation φ hφ p : Fiber φ x → Fiber φ x)^[n]) u = u ∧
      (∀ k : ℕ, 0 < k → k < n →
        ((pathPermutation φ hφ p : Fiber φ x → Fiber φ x)^[k]) u ≠ u) := by
  letI : Finite (Fiber φ x) := Subtype.finite
  exact exists_minimal_positive_return (pathPermutation φ hφ p) u

end MultigraphHom.Covering

end StrongRoberson
