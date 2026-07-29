import StrongRoberson.Proof.CoveringRepeat

/-!
# Splicing repeated lifted loops

The repetition API appends copies on the right.  For arguments that inspect
the first and last copies of a long repeated loop, it is useful to expose the
equivalent left-associated decomposition proved here.
-/

namespace Quiver.Path

/-- A nonempty repetition can equivalently be decomposed into its first copy
followed by all remaining copies. -/
theorem repeat_succ_left {V : Type*} [Quiver V] {x : V}
    (p : Path x x) (n : ℕ) :
    repeatClosed p (n + 1) = p.comp (repeatClosed p n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        repeatClosed p (n + 1 + 1) =
            (repeatClosed p (n + 1)).comp p := rfl
        _ = (p.comp (repeatClosed p n)).comp p := by rw [ih]
        _ = p.comp ((repeatClosed p n).comp p) :=
          Quiver.Path.comp_assoc _ _ _
        _ = p.comp (repeatClosed p (n + 1)) := rfl

/-- A repetition with two distinguished boundary copies is the first copy,
the middle `n` copies, and the final copy. -/
theorem repeat_add_two {V : Type*} [Quiver V] {x : V}
    (p : Path x x) (n : ℕ) :
    repeatClosed p (n + 2) =
      p.comp ((repeatClosed p n).comp p) := by
  calc
    repeatClosed p (n + 2) =
        (repeatClosed p (n + 1)).comp p := rfl
    _ = (p.comp (repeatClosed p n)).comp p := by
      rw [repeat_succ_left]
    _ = p.comp ((repeatClosed p n).comp p) :=
      Quiver.Path.comp_assoc _ _ _

end Quiver.Path

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- The lifted path of a nonempty repetition starts with the lift of the first
copy and then lifts all remaining copies from the transported fibre point. -/
theorem transportedPath_repeat_succ_left
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from x))
    (n : ℕ) (u : Fiber φ x) :
    transportedPath φ hφ (Quiver.Path.repeatClosed p (n + 1)) u ≍
      (transportedPath φ hφ p u).comp
        (transportedPath φ hφ (Quiver.Path.repeatClosed p n)
          (pathTransport φ hφ p u)) := by
  rw [Quiver.Path.repeat_succ_left]
  exact
    transportedPath_comp φ hφ p
      (Quiver.Path.repeatClosed p n) u

/-- The lifted path of `n + 2` repetitions, decomposed so that the first and
last lifted copies are explicit around the middle `n` repetitions. -/
theorem transportedPath_repeat_add_two
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ}
    (p : Quiver.Path (show Target G from x) (show Target G from x))
    (n : ℕ) (u : Fiber φ x) :
    transportedPath φ hφ (Quiver.Path.repeatClosed p (n + 2)) u ≍
      (transportedPath φ hφ p u).comp
        ((transportedPath φ hφ (Quiver.Path.repeatClosed p n)
            (pathTransport φ hφ p u)).comp
          (transportedPath φ hφ p
            (pathTransport φ hφ (Quiver.Path.repeatClosed p n)
              (pathTransport φ hφ p u)))) := by
  rw [Quiver.Path.repeat_add_two]
  let v := pathTransport φ hφ p u
  let a :=
    pathTransport φ hφ
      ((Quiver.Path.repeatClosed p n).comp p) v
  let b :=
    pathTransport φ hφ p
      (pathTransport φ hφ (Quiver.Path.repeatClosed p n) v)
  have hab : a = b :=
    pathTransport_comp φ hφ
      (Quiver.Path.repeatClosed p n) p v
  have habv : a.1 = b.1 :=
    congrArg Subtype.val hab
  have htail :
      transportedPath φ hφ
          ((Quiver.Path.repeatClosed p n).comp p) v ≍
        (transportedPath φ hφ
          (Quiver.Path.repeatClosed p n) v).comp
          (transportedPath φ hφ p
            (pathTransport φ hφ
              (Quiver.Path.repeatClosed p n) v)) :=
    transportedPath_comp φ hφ
      (Quiver.Path.repeatClosed p n) p v
  exact
    (transportedPath_comp φ hφ p
      ((Quiver.Path.repeatClosed p n).comp p) u).trans
      (Quiver.Path.comp_heq_of_eq
        (U := F.vertexSet)
        rfl rfl habv
        (transportedPath φ hφ p u)
        (transportedPath φ hφ
          ((Quiver.Path.repeatClosed p n).comp p) v)
        (transportedPath φ hφ p u)
        ((transportedPath φ hφ
          (Quiver.Path.repeatClosed p n) v).comp
          (transportedPath φ hφ p
            (pathTransport φ hφ
              (Quiver.Path.repeatClosed p n) v)))
        HEq.rfl htail)

end MultigraphHom.Covering

end StrongRoberson
