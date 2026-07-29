import StrongRoberson.Proof.CoveringReverse
import StrongRoberson.Proof.OutsidePath

/-!
# Transporting source-path avoidance through casts

`CoveringReverse` records that unique lifting commutes with reversal.  This
file adds the elementary `HEq` invariance of `SourcePath.Avoids`, eliminating
endpoint-cast bookkeeping from the chord argument.
-/

namespace StrongRoberson

namespace MultigraphHom.Covering

namespace SourcePath

/-- Avoidance is invariant under heterogeneous equality of paths. -/
theorem Avoids.of_heq
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v u' v' : F.vertexSet}
    {p : Quiver.Path u v} {q : Quiver.Path u' v'}
    (hp : Avoids B p)
    (hu : u = u') (hv : v = v') (hpq : p ≍ q) :
    Avoids B q := by
  subst u'
  subst v'
  have hpq' : p = q := eq_of_heq hpq
  subst q
  exact hp

/-- Convenient two-way form of avoidance invariance under `HEq`. -/
theorem avoids_heq_iff
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v u' v' : F.vertexSet}
    {p : Quiver.Path u v} {q : Quiver.Path u' v'}
    (hu : u = u') (hv : v = v') (hpq : p ≍ q) :
    Avoids B p ↔ Avoids B q :=
  ⟨fun hp ↦ hp.of_heq hu hv hpq,
    fun hq ↦ hq.of_heq hu.symm hv.symm hpq.symm⟩

/-- Changing the endpoint indices of a path preserves avoidance. -/
theorem Avoids.cast
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v u' v' : F.vertexSet}
    {p : Quiver.Path u v}
    (hp : Avoids B p) (hu : u = u') (hv : v = v') :
    Avoids B (p.cast hu hv) :=
  hp.of_heq hu hv (Quiver.Path.cast_heq hu hv p).symm

/-- Avoidance of an endpoint-cast path is equivalent to avoidance of the
underlying path. -/
@[simp]
theorem avoids_cast_iff
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v u' v' : F.vertexSet}
    (p : Quiver.Path u v) (hu : u = u') (hv : v = v') :
    Avoids B (p.cast hu hv) ↔ Avoids B p :=
  avoids_heq_iff hu.symm hv.symm
    (Quiver.Path.cast_heq hu hv p)

end SourcePath

end MultigraphHom.Covering

end StrongRoberson
