import StrongRoberson.Oddomorphism
import Mathlib.Combinatorics.Quiver.Covering

/-!
# Path lifting for perfect edge fibres

This file packages the local path-lifting argument used in the paper's
perfect-matching lemma.  The source quiver keeps every multigraph edge copy as
an arrow.  The target quiver has one arrow for every adjacency proof in the
simple target graph.

The perfect-fibre hypothesis says exactly that the induced prefunctor is
bijective on every star.  Since both quivers have involutive edge reversal,
this makes it a quiver covering, and Mathlib's covering API gives unique lifts
of arbitrary finite paths.
-/

open Set

namespace StrongRoberson

namespace MultigraphHom

/-- The edge-preimages of `φ` are perfect matchings between their endpoint
fibres.  Surjectivity is stated separately because isolated target vertices
have no incident edge on which the degree-one condition could detect them. -/
def HasPerfectFibers
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) : Prop :=
  Function.Surjective φ ∧
    ∀ (u : F.vertexSet) ⦃y : γ⦄, G.Adj (φ u) y →
      φ.edgeFiberDegree u y = 1

namespace Covering

/-- The quiver underlying an edge-typed multigraph.  Its arrows remember the
edge copy, so parallel edges remain distinct. -/
instance sourceQuiver {α β : Type*} (F : Graph α β) :
    Quiver F.vertexSet where
  Hom u v := {e : F.edgeSet // F.IsLink e.1 u.1 v.1}

/-- Reversing a source arrow keeps its edge copy and reverses its link proof. -/
instance sourceHasInvolutiveReverse {α β : Type*} (F : Graph α β) :
    Quiver.HasInvolutiveReverse F.vertexSet where
  reverse' e := ⟨e.1, e.2.symm⟩
  inv' e := by
    apply Subtype.ext
    rfl

/-- A type synonym carrying the quiver associated to a simple target graph.

The synonym is needed because the graph `G` cannot be recovered by typeclass
inference from its raw vertex type alone. -/
def Target {γ : Type*} (_G : SimpleGraph γ) := γ

/-- The target quiver has one arrow for each adjacency.  `PLift` promotes the
proposition-valued adjacency relation to the `Type` expected by `Quiver`. -/
instance targetQuiver {γ : Type*} (G : SimpleGraph γ) :
    Quiver (Target G) where
  Hom x y := PLift (G.Adj x y)

/-- Reversal in the target quiver is symmetry of adjacency. -/
instance targetHasInvolutiveReverse {γ : Type*} (G : SimpleGraph γ) :
    Quiver.HasInvolutiveReverse (Target G) where
  reverse' e := ⟨e.down.symm⟩
  inv' e := by
    apply PLift.down_injective
    apply Subsingleton.elim

/-- A multigraph homomorphism induces a prefunctor between the source and
target quivers. -/
def toPrefunctor
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) :
    F.vertexSet ⥤q Target G where
  obj := φ
  map e := ⟨φ.map_isLink e.2⟩

/-- The induced prefunctor respects reversal of undirected edges. -/
instance toPrefunctorMapReverse
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    (φ : MultigraphHom F G) :
    (toPrefunctor φ).MapReverse where
  map_reverse' _ := by
    apply PLift.down_injective
    apply Subsingleton.elim

/-- Perfect edge fibres make the induced map on the star of every source
vertex bijective.

Injectivity uses the uniqueness of the edge copy in the relevant fibre and
then uniqueness of the other endpoint of a link.  Surjectivity chooses the
unique edge copy counted by `edgeFiberDegree`. -/
theorem star_bijective
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) :
    Function.Bijective ((toPrefunctor φ).star u) := by
  constructor
  · rintro ⟨v, e⟩ ⟨w, e'⟩ h
    have htarget := congr_arg Sigma.fst h
    change φ v = φ w at htarget
    let S : Set F.edgeSet := {d | ∃ z : F.vertexSet,
      F.IsLink d.1 u.1 z.1 ∧ φ z = φ v}
    have heS : e.1 ∈ S := ⟨v, e.2, rfl⟩
    have heS' : e'.1 ∈ S := ⟨w, e'.2, htarget.symm⟩
    have hcard : S.ncard = 1 := by
      simpa only [MultigraphHom.edgeFiberDegree] using
        hφ.2 u (φ.map_isLink e.2)
    have hedges : e.1 = e'.1 :=
      ((Set.ncard_le_one (s := S))).mp (Nat.le_of_eq hcard)
        e.1 heS e'.1 heS'
    have hvw_val : v.1 = w.1 :=
      e.2.right_unique (hedges ▸ e'.2)
    have hvw : v = w := Subtype.ext hvw_val
    subst w
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    exact hedges
  · rintro ⟨y, hy⟩
    have hdeg := hφ.2 u hy.down
    let S : Set F.edgeSet := {e | ∃ v : F.vertexSet,
      F.IsLink e.1 u.1 v.1 ∧ φ v = y}
    have hS : S.ncard = 1 := by
      simpa only [MultigraphHom.edgeFiberDegree] using hdeg
    have hpos : 0 < S.ncard := by omega
    obtain ⟨e, heS⟩ := (Set.ncard_pos (s := S)).mp hpos
    obtain ⟨v, huv, hv⟩ := heS
    refine ⟨⟨v, ⟨e, huv⟩⟩, ?_⟩
    subst y
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    apply PLift.down_injective
    apply Subsingleton.elim

/-- A perfect-fibre homomorphism induces a covering of quivers. -/
theorem isCovering
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers) :
    (toPrefunctor φ).IsCovering :=
  Prefunctor.isCovering_of_bijective_star
    (toPrefunctor φ) (star_bijective φ hφ)

/-- Every target path beginning at `φ u` has a unique lift beginning at `u`. -/
theorem pathStar_bijective
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) :
    Function.Bijective ((toPrefunctor φ).pathStar u) :=
  (isCovering φ hφ).pathStar_bijective u

/-- The path-star equivalence supplied by unique path lifting. -/
noncomputable def pathStarEquiv
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) :
    Quiver.PathStar u ≃ Quiver.PathStar ((toPrefunctor φ).obj u) :=
  Equiv.ofBijective _ (pathStar_bijective φ hφ u)

/-- Lift a target path-star from the specified source vertex. -/
noncomputable def liftPathStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) :
    Quiver.PathStar ((toPrefunctor φ).obj u) → Quiver.PathStar u :=
  (pathStarEquiv φ hφ u).symm

@[simp]
theorem map_liftPathStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (p : Quiver.PathStar ((toPrefunctor φ).obj u)) :
    (toPrefunctor φ).pathStar u (liftPathStar φ hφ u p) = p :=
  (pathStarEquiv φ hφ u).apply_symm_apply p

@[simp]
theorem liftPathStar_map
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) (p : Quiver.PathStar u) :
    liftPathStar φ hφ u ((toPrefunctor φ).pathStar u p) = p :=
  (pathStarEquiv φ hφ u).symm_apply_apply p

/-- Existence and uniqueness of a lifted path-star, in proposition form. -/
theorem existsUnique_pathLift
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (p : Quiver.PathStar ((toPrefunctor φ).obj u)) :
    ∃! q : Quiver.PathStar u, (toPrefunctor φ).pathStar u q = p := by
  refine ⟨liftPathStar φ hφ u p, map_liftPathStar φ hφ u p, ?_⟩
  intro q hq
  rw [← hq]
  exact (liftPathStar_map φ hφ u q).symm

/-- Lift one explicitly endpoint-indexed target path.  The result packages its
source endpoint together with the lifted path. -/
noncomputable def liftPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) {y : Target G}
    (p : Quiver.Path ((toPrefunctor φ).obj u) y) :
    Quiver.PathStar u :=
  liftPathStar φ hφ u ⟨y, p⟩

@[simp]
theorem map_liftPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) {y : Target G}
    (p : Quiver.Path ((toPrefunctor φ).obj u) y) :
    (toPrefunctor φ).pathStar u (liftPath φ hφ u p) = ⟨y, p⟩ :=
  map_liftPathStar φ hφ u ⟨y, p⟩

/-- The endpoint of a lifted path lies over the endpoint of the target path. -/
theorem liftPath_endpoint
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) {y : Target G}
    (p : Quiver.Path ((toPrefunctor φ).obj u) y) :
    φ (liftPath φ hφ u p).1 = y := by
  exact congr_arg Sigma.fst (map_liftPath φ hφ u p)

/-- The path component of a lift maps to the given target path.  `HEq` is
appropriate because its endpoint equality is supplied separately by
`liftPath_endpoint`. -/
theorem map_liftPath_path
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) {y : Target G}
    (p : Quiver.Path ((toPrefunctor φ).obj u) y) :
    HEq ((toPrefunctor φ).mapPath (liftPath φ hφ u p).2) p := by
  exact (Sigma.mk.inj_iff.mp (map_liftPath φ hφ u p)).2

/-- Convert a simple-graph walk to the corresponding target-quiver path. -/
def walkToPath
    {γ : Type*} (G : SimpleGraph γ) {x y : γ} :
    G.Walk x y →
      Quiver.Path (show Target G from x) (show Target G from y)
  | .nil => .nil
  | .cons h p =>
      (Quiver.Hom.toPath
        (show PLift (G.Adj _ _) from ⟨h⟩)).comp (walkToPath G p)

@[simp]
theorem walkToPath_nil
    {γ : Type*} (G : SimpleGraph γ) (x : γ) :
    walkToPath G (SimpleGraph.Walk.nil : G.Walk x x) = .nil :=
  rfl

@[simp]
theorem walkToPath_cons
    {γ : Type*} (G : SimpleGraph γ) {x y z : γ}
    (h : G.Adj x y) (p : G.Walk y z) :
    walkToPath G (.cons h p) =
      (Quiver.Hom.toPath
        (show PLift (G.Adj x y) from ⟨h⟩)).comp (walkToPath G p) :=
  rfl

end Covering

end MultigraphHom

end StrongRoberson
