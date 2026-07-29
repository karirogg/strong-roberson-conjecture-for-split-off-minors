import StrongRoberson.Proof.LiftForest

/-!
# Source paths outside a protected branch set

`LiftForest` defines `SourcePath.Avoids B p`, proves that it is preserved by
composition and reversal, and turns an avoiding source-quiver path into an
`OutsideConnected` witness.  This file packages the symmetric and one-edge
forms used repeatedly by the chord-orbit argument.
-/

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- A length-zero path avoids `B` exactly when its sole vertex does. -/
theorem SourcePath.Avoids.nil
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u : F.vertexSet} (hu : u.1 ∉ B) :
    SourcePath.Avoids B
      (Quiver.Path.nil : Quiver.Path u u) :=
  hu

/-- A one-arrow path avoids `B` when both of its endpoints do. -/
theorem SourcePath.Avoids.toPath
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} (e : u ⟶ v)
    (hu : u.1 ∉ B) (hv : v.1 ∉ B) :
    SourcePath.Avoids B e.toPath :=
  ⟨hu, hv⟩

/-- Reversal preserves and reflects avoidance. -/
@[simp]
theorem SourcePath.avoids_reverse_iff
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} (p : Quiver.Path u v) :
    SourcePath.Avoids B p.reverse ↔
      SourcePath.Avoids B p := by
  constructor
  · intro hp
    have h := hp.reverse
    simpa only [Quiver.Path.reverse_reverse] using h
  · exact SourcePath.Avoids.reverse

/-- A composite source path avoids `B` exactly when both of its pieces do. -/
@[simp]
theorem SourcePath.avoids_comp_iff
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v w : F.vertexSet}
    (p : Quiver.Path u v) (q : Quiver.Path v w) :
    SourcePath.Avoids B (p.comp q) ↔
      SourcePath.Avoids B p ∧ SourcePath.Avoids B q := by
  induction q with
  | nil =>
      constructor
      · intro hp
        exact ⟨hp, hp.end_not_mem⟩
      · exact fun hp ↦ hp.1
  | cons q e ih =>
      change
        SourcePath.Avoids B (p.comp q) ∧ _ ↔
          SourcePath.Avoids B p ∧
            (SourcePath.Avoids B q ∧ _)
      rw [ih]
      tauto

/-- The left part of an avoiding composite path avoids `B`. -/
theorem SourcePath.Avoids.left_of_comp
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v w : F.vertexSet}
    {p : Quiver.Path u v} {q : Quiver.Path v w}
    (hpq : SourcePath.Avoids B (p.comp q)) :
    SourcePath.Avoids B p :=
  (SourcePath.avoids_comp_iff p q).mp hpq |>.1

/-- The right part of an avoiding composite path avoids `B`. -/
theorem SourcePath.Avoids.right_of_comp
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v w : F.vertexSet}
    {p : Quiver.Path u v} {q : Quiver.Path v w}
    (hpq : SourcePath.Avoids B (p.comp q)) :
    SourcePath.Avoids B q :=
  (SourcePath.avoids_comp_iff p q).mp hpq |>.2

/-- Method-style wrapper converting an avoiding path to its explicit outside
connectivity witness. -/
theorem SourcePath.Avoids.toOutsideConnected
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} {p : Quiver.Path u v}
    (hp : SourcePath.Avoids B p) :
    OutsideConnected F B u.1 v.1 :=
  SourcePath.outsideConnected p hp

/-- An avoiding path also supplies outside connectivity in the reverse
orientation. -/
theorem SourcePath.Avoids.toOutsideConnected_reverse
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} {p : Quiver.Path u v}
    (hp : SourcePath.Avoids B p) :
    OutsideConnected F B v.1 u.1 :=
  SourcePath.outsideConnected p.reverse hp.reverse

/-- Outside connectivity obtained from composed avoiding paths agrees with
the transitive composition of their individual connectivity witnesses. -/
theorem SourcePath.Avoids.comp_toOutsideConnected
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v w : F.vertexSet}
    {p : Quiver.Path u v} {q : Quiver.Path v w}
    (hp : SourcePath.Avoids B p) (hq : SourcePath.Avoids B q) :
    OutsideConnected F B u.1 w.1 :=
  StrongRoberson.MultigraphHom.Covering.OutsideConnected.trans
    hp.toOutsideConnected hq.toOutsideConnected

end MultigraphHom.Covering

end StrongRoberson
