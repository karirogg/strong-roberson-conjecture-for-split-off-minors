import StrongRoberson.Proof.CoveringConcat

/-!
# Repeating a closed path in a finite covering

The convention here appends one further copy on the right:
`repeat p (n + 1) = (repeat p n).comp p`.  With the transport-composition
orientation from `CoveringConcat`, this agrees with `Function.iterate`.
-/

namespace Quiver.Path

/-- Repeat a closed quiver path `n` times, appending each new copy on the
right. -/
def repeatClosed {V : Type*} [Quiver V] {x : V}
    (p : Path x x) : ℕ → Path x x
  | 0 => .nil
  | n + 1 => (repeatClosed p n).comp p

@[simp]
theorem repeat_zero {V : Type*} [Quiver V] {x : V}
    (p : Path x x) :
    repeatClosed p 0 = .nil :=
  rfl

@[simp]
theorem repeat_succ {V : Type*} [Quiver V] {x : V}
    (p : Path x x) (n : ℕ) :
    repeatClosed p (n + 1) = (repeatClosed p n).comp p :=
  rfl

end Quiver.Path

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- Transport along the empty target path fixes its source vertex. -/
@[simp]
theorem pathTransport_nil
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ} (u : Fiber φ x) :
    pathTransport φ hφ
      (Quiver.Path.nil :
        Quiver.Path (show Target G from x) (show Target G from x))
      u = u := by
  let r : Quiver.PathStar u.1 :=
    ⟨u.1, Quiver.Path.nil⟩
  have huT :
      (show Target G from φ u.1) =
        (show Target G from x) :=
    u.2
  have hr :
      (toPrefunctor φ).pathStar u.1 r =
        ⟨(show Target G from x),
          targetPathAt φ
            (Quiver.Path.nil :
              Quiver.Path (show Target G from x)
                (show Target G from x))
            u⟩ := by
    refine Sigma.ext u.2 ?_
    change
      (Quiver.Path.nil :
        Quiver.Path (show Target G from φ u.1)
          (show Target G from φ u.1)) ≍
        targetPathAt φ
          (Quiver.Path.nil :
            Quiver.Path (show Target G from x)
              (show Target G from x))
          u
    exact
      ((Quiver.Path.cast_heq (U := Target G) huT huT
          (Quiver.Path.nil :
            Quiver.Path (show Target G from φ u.1)
              (show Target G from φ u.1))).symm).trans
        ((heq_of_eq (Quiver.Path.cast_nil huT)).trans
          (targetPathAt_heq φ Quiver.Path.nil u).symm)
  apply Subtype.ext
  change
    (liftPathStar φ hφ u.1
      ⟨(show Target G from x),
        targetPathAt φ
          (Quiver.Path.nil :
            Quiver.Path (show Target G from x)
              (show Target G from x))
          u⟩).1 = u.1
  rw [← hr]
  exact congrArg Sigma.fst (liftPathStar_map φ hφ u.1 r)

/-- Transport along `n` repetitions of a closed target path is its `n`-fold
function iterate. -/
@[simp]
theorem pathTransport_repeat
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from x))
    (n : ℕ) (u : Fiber φ x) :
    pathTransport φ hφ (Quiver.Path.repeatClosed p n) u =
      (pathTransport φ hφ p)^[n] u := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Quiver.Path.repeat_succ, pathTransport_comp, ih,
        Function.iterate_succ_apply']

/-- Changing a fibre element by equality changes its transported lift only
heterogeneously. -/
theorem transportedPath_heq_of_eq
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

/-- The lift of `n + 1` copies decomposes into the lift of the first `n`
copies followed by the lift of one copy from the `n`th orbit point.

The cast changes only the endpoint index of the first lifted path, using
`pathTransport_repeat`; the path itself is unchanged up to `HEq`.
-/
theorem transportedPath_repeat_succ
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from x))
    (n : ℕ) (u : Fiber φ x) :
    transportedPath φ hφ (Quiver.Path.repeatClosed p (n + 1)) u ≍
      ((transportedPath φ hφ (Quiver.Path.repeatClosed p n) u).cast
          rfl
          (congrArg Subtype.val
            (pathTransport_repeat φ hφ p n u))).comp
        (transportedPath φ hφ p
          ((pathTransport φ hφ p)^[n] u)) := by
  rw [Quiver.Path.repeat_succ]
  let a := pathTransport φ hφ
    (Quiver.Path.repeatClosed p n) u
  let b := (pathTransport φ hφ p)^[n] u
  have hab : a = b :=
    pathTransport_repeat φ hφ p n u
  have habv : a.1 = b.1 :=
    congrArg Subtype.val hab
  have hnext :
      (pathTransport φ hφ p a).1 =
        (pathTransport φ hφ p b).1 :=
    congrArg Subtype.val
      (congrArg (pathTransport φ hφ p) hab)
  have hp :
      transportedPath φ hφ
          (Quiver.Path.repeatClosed p n) u ≍
        (transportedPath φ hφ
          (Quiver.Path.repeatClosed p n) u).cast
            rfl habv :=
    (Quiver.Path.cast_heq rfl habv _).symm
  have hq :
      transportedPath φ hφ p a ≍
        transportedPath φ hφ p b :=
    transportedPath_heq_of_eq φ hφ p hab
  exact
    (transportedPath_comp φ hφ
      (Quiver.Path.repeatClosed p n) p u).trans
      (Quiver.Path.comp_heq_of_eq
        (U := F.vertexSet)
        rfl habv hnext
        (transportedPath φ hφ
          (Quiver.Path.repeatClosed p n) u)
        (transportedPath φ hφ p a)
        ((transportedPath φ hφ
          (Quiver.Path.repeatClosed p n) u).cast
            rfl habv)
        (transportedPath φ hφ p b)
        hp hq)

end MultigraphHom.Covering

end StrongRoberson
