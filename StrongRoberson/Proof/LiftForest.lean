import StrongRoberson.Proof.CoveringRepeat
import StrongRoberson.Proof.CollapseOutside

/-!
# A coherently lifted full spanning forest

This file develops the spanning-forest part of the paper's proof of the
perfect-fibre lemma.  A maximal acyclic subgraph of the target is chosen, one
source root is chosen above each target component, and unique path lifting
selects one coherent source branch vertex above every target vertex.

The source paths live in the edge-copy quiver from `Proof.Covering`, so
parallel multigraph edges remain distinct throughout.
-/

namespace Graph

/-- The loopless simple shadow of an edge-typed graph on its live vertices.

Parallel edge copies induce the same adjacency, while loops are deliberately
discarded.  This is the appropriate graph for connectivity statements that
do not count edge multiplicity. -/
def nonloopShadow
    {α β : Type*} (F : Graph α β) :
    SimpleGraph F.vertexSet :=
  SimpleGraph.fromRel fun u v => F.Adj u.1 v.1

@[simp]
theorem nonloopShadow_adj
    {α β : Type*} (F : Graph α β) (u v : F.vertexSet) :
    F.nonloopShadow.Adj u v ↔ u ≠ v ∧ F.Adj u.1 v.1 := by
  simp [nonloopShadow, SimpleGraph.fromRel_adj, Graph.adj_comm]

end Graph

namespace StrongRoberson

/-- A full spanning forest of `G`: it is acyclic, contained in `G`, and has
exactly the same reachability relation as `G`. -/
structure FullSpanningForest {γ : Type*} (G : SimpleGraph γ) where
  graph : SimpleGraph γ
  le_target : graph ≤ G
  isAcyclic : graph.IsAcyclic
  reachable_eq : graph.Reachable = G.Reachable

namespace FullSpanningForest

/-- Choose a full spanning forest by extending the empty graph to a maximal
acyclic subgraph. -/
noncomputable def choose {γ : Type*} (G : SimpleGraph γ) :
    FullSpanningForest G := by
  let hex := G.exists_maximal_isAcyclic_of_le_isAcyclic
    (H := ⊥) bot_le SimpleGraph.isAcyclic_bot
  let T := Classical.choose hex
  have hmax := (Classical.choose_spec hex).2
  exact
    ⟨T, hmax.prop.1, hmax.prop.2,
      G.reachable_eq_of_maximal_isAcyclic T hmax⟩

/-- A chosen vertex of a target connected component. -/
noncomputable def componentRoot
    {γ : Type*} {G : SimpleGraph γ} (c : G.ConnectedComponent) : γ :=
  Classical.choose c.nonempty_supp

theorem componentRoot_mem
    {γ : Type*} {G : SimpleGraph γ} (c : G.ConnectedComponent) :
    componentRoot c ∈ c.supp :=
  Classical.choose_spec c.nonempty_supp

/-- A chosen source vertex above the root of a target component. -/
noncomputable def sourceRoot
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (c : G.ConnectedComponent) : F.vertexSet :=
  Classical.choose (hφ.1 (componentRoot c))

@[simp]
theorem map_sourceRoot
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (c : G.ConnectedComponent) :
    φ (sourceRoot φ hφ c) = componentRoot c :=
  Classical.choose_spec (hφ.1 (componentRoot c))

/-- The chosen target forest connects the image of the source root to every
vertex in its target component. -/
theorem componentReachable
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    T.graph.Reachable (φ (sourceRoot φ hφ c)) v.1 := by
  rw [map_sourceRoot, T.reachable_eq]
  exact c.reachable_of_mem_supp (componentRoot_mem c) v.2

/-- The unique simple forest path from the chosen component root to `v`.

`Reachable.some.toPath` only chooses an initial path; acyclicity makes the
result independent of that choice propositionally. -/
noncomputable def componentPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    T.graph.Path (φ (sourceRoot φ hφ c)) v.1 := by
  classical
  exact (componentReachable φ hφ T c v).some.toPath

end FullSpanningForest

namespace MultigraphHom.Covering

/-- Concatenate two explicit outside connections. -/
theorem OutsideConnected.trans
    {α β : Type*} {F : Graph α β} {B : Set α}
    {x y z : α}
    (hxy : OutsideConnected F B x y)
    (hyz : OutsideConnected F B y z) :
    OutsideConnected F B x z := by
  induction hyz with
  | refl => exact hxy
  | tail _ hyz hz ih => exact .tail ih hyz hz

/-- Reverse an explicit outside connection. -/
theorem OutsideConnected.symm
    {α β : Type*} {F : Graph α β} {B : Set α}
    {x y : α}
    (hxy : OutsideConnected F B x y) :
    OutsideConnected F B y x := by
  induction hxy with
  | refl hx => exact .refl hx
  | tail hxy hyz hz ih =>
      exact
        StrongRoberson.MultigraphHom.Covering.OutsideConnected.trans
          (OutsideConnected.tail (OutsideConnected.refl hz)
            hyz.symm hxy.right_not_mem) ih

/-- Every vertex of an edge-copy quiver path lies outside `B`. -/
def SourcePath.Avoids
    {α β : Type*} {F : Graph α β} (B : Set α)
    {u : F.vertexSet} :
    ∀ {v : F.vertexSet}, Quiver.Path u v → Prop
  | _, .nil => u.1 ∉ B
  | v, .cons p _ => SourcePath.Avoids B p ∧ v.1 ∉ B

/-- A source-quiver path avoiding `B` is an explicit outside connection in
the edge-typed graph. -/
theorem SourcePath.outsideConnected
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} (p : Quiver.Path u v)
    (hp : SourcePath.Avoids B p) :
    OutsideConnected F B u.1 v.1 := by
  induction p with
  | nil => exact .refl hp
  | cons p e ih =>
      exact .tail (ih hp.1) e.2 hp.2

/-- Avoidance is preserved by path composition. -/
theorem SourcePath.Avoids.comp
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v w : F.vertexSet}
    {p : Quiver.Path u v} {q : Quiver.Path v w}
    (hp : SourcePath.Avoids B p) (hq : SourcePath.Avoids B q) :
    SourcePath.Avoids B (p.comp q) := by
  induction q with
  | nil => exact hp
  | cons q e ih => exact ⟨ih hq.1, hq.2⟩

/-- Recursive path avoidance is equivalent to excluding every vertex in the
standard vertex list. -/
theorem SourcePath.avoids_iff_vertices
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} (p : Quiver.Path u v) :
    SourcePath.Avoids B p ↔
      ∀ z ∈ p.vertices, z.1 ∉ B := by
  induction p with
  | nil =>
      simp [SourcePath.Avoids]
  | cons p e ih =>
      rw [SourcePath.Avoids, ih]
      constructor
      · rintro ⟨hp, hc⟩ z hz
        rw [Quiver.Path.mem_vertices_cons] at hz
        exact hz.elim (hp z) (fun h ↦ h ▸ hc)
      · intro h
        refine ⟨fun z hz ↦ h z ?_, h _ ?_⟩
        · rw [Quiver.Path.mem_vertices_cons]
          exact Or.inl hz
        · rw [Quiver.Path.mem_vertices_cons]
          exact Or.inr rfl

/-- The initial vertex of an avoiding source path is outside the protected
set. -/
theorem SourcePath.Avoids.start_not_mem
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} {p : Quiver.Path u v}
    (hp : SourcePath.Avoids B p) :
    u.1 ∉ B :=
  (SourcePath.avoids_iff_vertices p).mp hp u p.start_mem_vertices

/-- The final vertex of an avoiding source path is outside the protected
set. -/
theorem SourcePath.Avoids.end_not_mem
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} {p : Quiver.Path u v}
    (hp : SourcePath.Avoids B p) :
    v.1 ∉ B :=
  (SourcePath.avoids_iff_vertices p).mp hp v p.end_mem_vertices

/-- Reversing a source path preserves its set of visited vertices and hence
preserves avoidance. -/
theorem SourcePath.Avoids.reverse
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} {p : Quiver.Path u v}
    (hp : SourcePath.Avoids B p) :
    SourcePath.Avoids B p.reverse := by
  induction p with
  | nil => exact hp
  | cons p e ih =>
      have hedge :
          SourcePath.Avoids B (Quiver.reverse e).toPath :=
        ⟨hp.2, hp.1.end_not_mem⟩
      exact hedge.comp (ih hp.1)

/-- Append one outgoing arrow to a path-star. -/
def PathStar.extend
    {V : Type*} [Quiver V] {u : V}
    (p : Quiver.PathStar u) (e : Quiver.Star p.1) :
    Quiver.PathStar u :=
  ⟨e.1, p.2.comp e.2.toPath⟩

@[simp]
theorem PathStar.extend_fst
    {V : Type*} [Quiver V] {u : V}
    (p : Quiver.PathStar u) (e : Quiver.Star p.1) :
    (PathStar.extend p e).1 = e.1 :=
  rfl

@[simp]
theorem PathStar.map_extend
    {U V : Type*} [Quiver U] [Quiver V]
    (ψ : U ⥤q V) {u : U}
    (p : Quiver.PathStar u) (e : Quiver.Star p.1) :
    ψ.pathStar u (PathStar.extend p e) =
      PathStar.extend (ψ.pathStar u p) (ψ.star p.1 e) := by
  rfl

/-- Lift one further target arrow after an already lifted path-star. -/
theorem exists_extend_preimage
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet) (q : Quiver.PathStar u)
    (p : Quiver.PathStar ((toPrefunctor φ).obj u))
    (hq : (toPrefunctor φ).pathStar u q = p)
    (h : Quiver.Star p.1) :
    ∃ s : Quiver.Star q.1,
      (toPrefunctor φ).pathStar u (PathStar.extend q s) =
        PathStar.extend p h := by
  subst p
  obtain ⟨s, hs⟩ := (star_bijective φ hφ q.1).2 h
  refine ⟨s, ?_⟩
  rw [PathStar.map_extend, hs]

/-- The endpoints of the lifts of `p` and of its one-arrow extension are
joined by a direct source arrow. -/
theorem liftPathStar_extend_nonempty
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (p : Quiver.PathStar ((toPrefunctor φ).obj u))
    (h : Quiver.Star p.1) :
    Nonempty
      ((liftPathStar φ hφ u p).1 ⟶
        (liftPathStar φ hφ u (PathStar.extend p h)).1) := by
  let q := liftPathStar φ hφ u p
  obtain ⟨s, hs⟩ :=
    exists_extend_preimage φ hφ u q p
      (map_liftPathStar φ hφ u p) h
  have hext :
      PathStar.extend q s =
        liftPathStar φ hφ u (PathStar.extend p h) := by
    apply (pathStar_bijective φ hφ u).1
    rw [hs, map_liftPathStar]
  have hend :
      s.1 = (liftPathStar φ hφ u (PathStar.extend p h)).1 :=
    congr_arg Sigma.fst hext
  rw [← hend]
  exact ⟨s.2⟩

/-- Lifting a single target arrow produces a concrete source edge from the
chosen point to the transported endpoint. -/
theorem exists_isLink_pathTransport_toPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u : F.vertexSet)
    (h : Quiver.Star ((toPrefunctor φ).obj u)) :
    ∃ e : F.edgeSet,
      F.IsLink e.1 u.1
        (pathTransport φ hφ h.2.toPath
          (show Fiber φ (φ u) from ⟨u, rfl⟩)).1.1 := by
  let p0 : Quiver.PathStar ((toPrefunctor φ).obj u) :=
    ⟨(toPrefunctor φ).obj u, Quiver.Path.nil⟩
  have hnil :
      liftPathStar φ hφ u p0 =
        ⟨u, Quiver.Path.nil⟩ := by
    exact liftPathStar_map φ hφ u
      (show Quiver.PathStar u from
        ⟨u, Quiver.Path.nil⟩)
  have hext :=
    liftPathStar_extend_nonempty φ hφ u p0 h
  rw [hnil] at hext
  obtain ⟨e⟩ := hext
  exact ⟨e.1, e.2⟩

/-- Fibre-indexed form of `exists_isLink_pathTransport_toPath`, with the
necessary start-point cast handled internally by `pathTransport`. -/
theorem exists_isLink_pathTransport_toPathAt
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (h : (show Target G from x) ⟶ (show Target G from y))
    (u : Fiber φ x) :
    ∃ e : F.edgeSet,
      F.IsLink e.1 u.1.1
        (pathTransport φ hφ h.toPath u).1.1 := by
  rcases u with ⟨u, hu⟩
  subst x
  exact exists_isLink_pathTransport_toPath φ hφ u ⟨y, h⟩

/-- At a fixed source vertex, two outgoing edge copies with equally mapped
other endpoints coincide under the perfect-fibre hypothesis. -/
theorem sourceArrow_edge_eq_of_endpoint_image_eq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (u v w : F.vertexSet)
    (e e' : F.edgeSet)
    (he : F.IsLink e.1 u.1 v.1)
    (he' : F.IsLink e'.1 u.1 w.1)
    (hvw : φ v = φ w) :
    e = e' := by
  let S : Set F.edgeSet := {d | ∃ z : F.vertexSet,
    F.IsLink d.1 u.1 z.1 ∧ φ z = φ v}
  have heS : e ∈ S := ⟨v, he, rfl⟩
  have heS' : e' ∈ S := ⟨w, he', hvw.symm⟩
  have hcard : S.ncard = 1 := by
    simpa only [MultigraphHom.edgeFiberDegree] using
      hφ.2 u (φ.map_isLink he)
  exact ((Set.ncard_le_one (s := S))).mp (Nat.le_of_eq hcard)
    e heS e' heS'

set_option backward.isDefEq.respectTransparency false in
/-- Mapping a walk to a supergraph commutes with appending its final edge. -/
theorem walk_mapLe_concat
    {γ : Type*} {T G : SimpleGraph γ} (hle : T ≤ G)
    {x y z : γ} (p : T.Walk x y) (h : T.Adj y z) :
    (p.concat h).mapLe hle = (p.mapLe hle).concat (hle h) := by
  induction p with
  | nil => rfl
  | cons _ p ih =>
      change
        SimpleGraph.Walk.cons _ ((p.concat h).mapLe hle) =
          SimpleGraph.Walk.cons _ ((p.mapLe hle).concat (hle h))
      congr 1
      exact ih h

/-- Converting a walk to a quiver path commutes with appending its final
edge. -/
theorem walkToPath_concat
    {γ : Type*} (G : SimpleGraph γ)
    {x y z : γ} (p : G.Walk x y) (h : G.Adj y z) :
    walkToPath G (p.concat h) =
      (walkToPath G p).comp
        (Quiver.Hom.toPath
          (show PLift (G.Adj y z) from ⟨h⟩)) := by
  induction p with
  | nil =>
      rw [SimpleGraph.Walk.concat_nil, walkToPath_cons, walkToPath_nil]
      rfl
  | cons _ p ih =>
      simp only [SimpleGraph.Walk.concat_cons, walkToPath_cons]
      rw [ih, Quiver.Path.comp_assoc]

/-- The target vertex below the selected source root of a component. -/
noncomputable def componentRootTarget
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (c : G.ConnectedComponent) : γ :=
  φ (FullSpanningForest.sourceRoot φ hφ c)

/-- The target path-star from the chosen component root to `v`. -/
noncomputable def componentTargetPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    Quiver.PathStar
      ((toPrefunctor φ).obj
        (FullSpanningForest.sourceRoot φ hφ c)) :=
  ⟨v.1,
    walkToPath G
      ((FullSpanningForest.componentPath φ hφ T c v).1.mapLe
        T.le_target)⟩

/-- Endpoint-explicit path component of `componentTargetPath`. -/
noncomputable def componentTargetPathPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    Quiver.Path
      (show Target G from componentRootTarget (γ := γ) φ hφ c)
      (show Target G from v.1) :=
  (componentTargetPath φ hφ T c v).2

/-- The target-quiver arrow associated to one oriented forest edge. -/
noncomputable def componentTargetEdge
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    {x y : c.supp} (hxy : T.graph.Adj x.1 y.1) :
    Quiver.Star (componentTargetPath φ hφ T c x).1 :=
  ⟨y.1, ⟨T.le_target hxy⟩⟩

/-- The target-quiver arrow corresponding to an arbitrary oriented target
edge. -/
def targetChordArrow
    {γ : Type*} {G : SimpleGraph γ} {x y : γ}
    (hxy : G.Adj x y) :
    (show Target G from x) ⟶ (show Target G from y) :=
  ⟨hxy⟩

/-- The fundamental closed target path obtained from the root-to-`x` forest
path, the chord `xy`, and the reverse root-to-`y` forest path. -/
noncomputable def componentFundamentalLoop
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    Quiver.Path
      (show Target G from componentRootTarget (γ := γ) φ hφ c)
      (show Target G from componentRootTarget (γ := γ) φ hφ c) :=
  ((componentTargetPathPath φ hφ T c x).comp
      (targetChordArrow hxy).toPath).comp
    (componentTargetPathPath φ hφ T c y).reverse

/-- The selected source root, regarded as a point in the root fibre on which
the fundamental-loop monodromy acts. -/
noncomputable def componentRootFiber
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (c : G.ConnectedComponent) :
    Fiber φ (componentRootTarget (γ := γ) φ hφ c) :=
  ⟨FullSpanningForest.sourceRoot φ hφ c, rfl⟩

/-- Monodromy of one traversal of a chord's fundamental target loop. -/
noncomputable def componentChordPermutation
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    Equiv.Perm
      (Fiber φ (componentRootTarget (γ := γ) φ hφ c)) :=
  pathPermutation φ hφ
    (componentFundamentalLoop φ hφ T c x y hxy)

/-- The least positive number of fundamental-loop traversals returning the
selected source root to itself. -/
noncomputable def componentChordReturnTime
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) : ℕ :=
  letI : Finite
      (Fiber φ (componentRootTarget (γ := γ) φ hφ c)) :=
    Subtype.finite
  minimalReturnTime
    (componentChordPermutation φ hφ T c x y hxy)
    (componentRootFiber φ hφ c)

/-- The fundamental-loop return time is positive. -/
theorem componentChordReturnTime_pos
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    0 < componentChordReturnTime φ hφ T c x y hxy := by
  letI : Finite
      (Fiber φ (componentRootTarget (γ := γ) φ hφ c)) :=
    Subtype.finite
  exact minimalReturnTime_pos
    (componentChordPermutation φ hφ T c x y hxy)
    (componentRootFiber φ hφ c)

/-- At the least return time, the fundamental-loop monodromy returns the
selected source root. -/
theorem componentChordReturnTime_apply
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    ((componentChordPermutation φ hφ T c x y hxy :
        Fiber φ (componentRootTarget (γ := γ) φ hφ c) →
        Fiber φ (componentRootTarget (γ := γ) φ hφ c))^[
      componentChordReturnTime φ hφ T c x y hxy])
        (componentRootFiber φ hφ c) =
      componentRootFiber φ hφ c := by
  letI : Finite
      (Fiber φ (componentRootTarget (γ := γ) φ hφ c)) :=
    Subtype.finite
  exact iterate_minimalReturnTime
    (componentChordPermutation φ hφ T c x y hxy)
    (componentRootFiber φ hφ c)

/-- No earlier positive number of fundamental-loop traversals returns the
selected source root. -/
theorem componentChordReturnTime_minimal
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    {k : ℕ} (hk : 0 < k)
    (hlt : k < componentChordReturnTime φ hφ T c x y hxy) :
    ((componentChordPermutation φ hφ T c x y hxy :
        Fiber φ (componentRootTarget (γ := γ) φ hφ c) →
        Fiber φ (componentRootTarget (γ := γ) φ hφ c))^[k])
        (componentRootFiber φ hφ c) ≠
      componentRootFiber φ hφ c := by
  letI : Finite
      (Fiber φ (componentRootTarget (γ := γ) φ hφ c)) :=
    Subtype.finite
  exact iterate_ne_of_pos_lt_minimalReturnTime
    (componentChordPermutation φ hφ T c x y hxy)
    (componentRootFiber φ hφ c) hk hlt

/-- The `k`th root-fibre point in the fundamental-loop orbit. -/
noncomputable def componentChordOrbitRoot
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    Fiber φ (componentRootTarget (γ := γ) φ hφ c) :=
  ((componentChordPermutation φ hφ T c x y hxy :
      Fiber φ (componentRootTarget (γ := γ) φ hφ c) →
      Fiber φ (componentRootTarget (γ := γ) φ hφ c))^[k])
    (componentRootFiber φ hφ c)

/-- Every strictly intermediate root-orbit point differs from the selected
root. -/
theorem componentChordOrbitRoot_ne_main
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    {k : ℕ} (hk : 0 < k)
    (hlt : k < componentChordReturnTime φ hφ T c x y hxy) :
    componentChordOrbitRoot φ hφ T c x y hxy k ≠
      componentRootFiber φ hφ c := by
  exact componentChordReturnTime_minimal
    φ hφ T c x y hxy hk hlt

/-- The root-orbit point at the return time is the selected root. -/
@[simp]
theorem componentChordOrbitRoot_return
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    componentChordOrbitRoot φ hφ T c x y hxy
        (componentChordReturnTime φ hφ T c x y hxy) =
      componentRootFiber φ hφ c :=
  componentChordReturnTime_apply φ hφ T c x y hxy

/-- The point above `x` reached from the `k`th root-orbit point along the
chosen root-to-`x` forest path. -/
noncomputable def componentChordOrbitX
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    Fiber φ x.1 :=
  pathTransport φ hφ
    (componentTargetPathPath φ hφ T c x)
    (componentChordOrbitRoot φ hφ T c x y hxy k)

/-- The point above `y` reached after the chord in the `k`th traversal. -/
noncomputable def componentChordOrbitY
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    Fiber φ y.1 :=
  pathTransport φ hφ (targetChordArrow hxy).toPath
    (componentChordOrbitX φ hφ T c x y hxy k)

/-- Completing the reverse `y`-forest segment advances the root orbit by one
fundamental-loop traversal. -/
theorem componentChordOrbitRoot_succ
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    pathTransport φ hφ
        (componentTargetPathPath φ hφ T c y).reverse
        (componentChordOrbitY φ hφ T c x y hxy k) =
      componentChordOrbitRoot φ hφ T c x y hxy (k + 1) := by
  let px := componentTargetPathPath φ hφ T c x
  let ch := (targetChordArrow hxy).toPath
  let ry := (componentTargetPathPath φ hφ T c y).reverse
  let rk := componentChordOrbitRoot φ hφ T c x y hxy k
  have hinner :=
    pathTransport_comp
      (α := α) (β := β) (γ := γ) (F := F) (G := G)
      (x := componentRootTarget (γ := γ) φ hφ c)
      (y := x.1) (z := y.1) φ hφ px ch rk
  have houter :=
    pathTransport_comp
      (α := α) (β := β) (γ := γ) (F := F) (G := G)
      (x := componentRootTarget (γ := γ) φ hφ c)
      (y := y.1)
      (z := componentRootTarget (γ := γ) φ hφ c)
      φ hφ (px.comp ch) ry rk
  have hstep :
      componentChordOrbitRoot φ hφ T c x y hxy (k + 1) =
        pathTransport φ hφ
          (componentFundamentalLoop φ hφ T c x y hxy) rk := by
    simp only [componentChordOrbitRoot,
      Function.iterate_succ_apply',
      componentChordPermutation, pathPermutation,
      pathTransportEquiv_apply, rk]
  calc
    pathTransport φ hφ ry
        (componentChordOrbitY φ hφ T c x y hxy k) =
      pathTransport φ hφ ry
        (pathTransport φ hφ (px.comp ch) rk) := by
          exact congr_arg (pathTransport φ hφ ry) hinner.symm
    _ = pathTransport φ hφ
        ((px.comp ch).comp ry) rk :=
      houter.symm
    _ = pathTransport φ hφ
        (componentFundamentalLoop φ hφ T c x y hxy) rk := by
      rfl
    _ = componentChordOrbitRoot φ hφ T c x y hxy (k + 1) :=
      hstep.symm

@[simp]
theorem componentChordOrbitRoot_zero
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    componentChordOrbitRoot φ hφ T c x y hxy 0 =
      componentRootFiber φ hφ c := by
  simp [componentChordOrbitRoot]

/-- Along a forest edge, exactly one of the two chosen root paths is obtained
from the other by appending that edge. -/
theorem componentTargetPath_adj
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    {x y : c.supp} (hxy : T.graph.Adj x.1 y.1) :
    componentTargetPath φ hφ T c y =
        PathStar.extend (componentTargetPath φ hφ T c x)
          (componentTargetEdge φ hφ T c hxy) ∨
      componentTargetPath φ hφ T c x =
        PathStar.extend (componentTargetPath φ hφ T c y)
          (componentTargetEdge φ hφ T c hxy.symm) := by
  classical
  let px := FullSpanningForest.componentPath φ hφ T c x
  let py := FullSpanningForest.componentPath φ hφ T c y
  by_cases hx : x.1 ∈ py.1.support
  · left
    have hwalk : py.1 = px.1.concat hxy :=
      T.isAcyclic.path_concat px.2 py.2 hxy hx
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change
      walkToPath G (py.1.mapLe T.le_target) =
        (walkToPath G (px.1.mapLe T.le_target)).comp
          (Quiver.Hom.toPath
            (show PLift (G.Adj x.1 y.1) from
              ⟨T.le_target hxy⟩))
    rw [hwalk, walk_mapLe_concat, walkToPath_concat]
  · right
    have hy : y.1 ∈ px.1.support :=
      T.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
        px.2 py.2 hxy hx
    have hwalk : px.1 = py.1.concat hxy.symm :=
      T.isAcyclic.path_concat py.2 px.2 hxy.symm hy
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    change
      walkToPath G (px.1.mapLe T.le_target) =
        (walkToPath G (py.1.mapLe T.le_target)).comp
          (Quiver.Hom.toPath
            (show PLift (G.Adj y.1 x.1) from
              ⟨T.le_target hxy.symm⟩))
    rw [hwalk, walk_mapLe_concat, walkToPath_concat]

/-- The source branch vertex selected by lifting the forest path to `v`. -/
noncomputable def componentBranch
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    F.vertexSet :=
  (liftPathStar φ hφ
    (FullSpanningForest.sourceRoot φ hφ c)
    (componentTargetPath φ hφ T c v)).1

@[simp]
theorem map_componentBranch
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    φ (componentBranch φ hφ T c v) = v.1 := by
  exact congr_arg Sigma.fst
    (map_liftPathStar φ hφ
      (FullSpanningForest.sourceRoot φ hφ c)
      (componentTargetPath φ hφ T c v))

/-- The selected component branch vertex, packaged in its target fibre. -/
noncomputable def componentBranchFiber
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    Fiber φ v.1 :=
  ⟨componentBranch φ hφ T c v,
    map_componentBranch φ hφ T c v⟩

/-- The selected branch fibre point is transport of the selected root along
the chosen forest path. -/
theorem componentBranchFiber_eq_pathTransport
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    componentBranchFiber φ hφ T c v =
      pathTransport φ hφ
        (componentTargetPathPath φ hφ T c v)
        (componentRootFiber φ hφ c) := by
  apply Subtype.ext
  rfl

/-- The first point above `x` in the fundamental-loop orbit is the selected
branch vertex above `x`. -/
@[simp]
theorem componentChordOrbitX_zero
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    componentChordOrbitX φ hφ T c x y hxy 0 =
      componentBranchFiber φ hφ T c x := by
  rw [componentChordOrbitX, componentChordOrbitRoot_zero,
    componentBranchFiber_eq_pathTransport]

/-- Transport a point above `v` backwards along the chosen forest path.  This
is its sheet label in the root fibre. -/
noncomputable def componentSheetRoot
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) (u : Fiber φ v.1) :
    Fiber φ (componentRootTarget (γ := γ) φ hφ c) :=
  pathTransport φ hφ
    (componentTargetPathPath φ hφ T c v).reverse u

/-- The sheet label of a selected branch vertex is the selected root. -/
@[simp]
theorem componentSheetRoot_branch
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    componentSheetRoot φ hφ T c v
        (componentBranchFiber φ hφ T c v) =
      componentRootFiber φ hφ c := by
  rw [componentBranchFiber_eq_pathTransport]
  change
    pathTransport φ hφ
        (componentTargetPathPath φ hφ T c v).reverse
          (pathTransport φ hφ
          (componentTargetPathPath φ hφ T c v)
          (componentRootFiber φ hφ c)) =
      componentRootFiber φ hφ c
  exact pathTransport_reverse_apply φ hφ
    (componentTargetPathPath φ hφ T c v)
    (componentRootFiber φ hφ c)

/-- The sheet label of the point above `x` in the `k`th traversal is the
`k`th root-orbit point. -/
theorem componentSheetRoot_orbitX
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    componentSheetRoot φ hφ T c x
        (componentChordOrbitX φ hφ T c x y hxy k) =
      componentChordOrbitRoot φ hφ T c x y hxy k := by
  exact pathTransport_reverse_apply φ hφ
    (componentTargetPathPath φ hφ T c x)
    (componentChordOrbitRoot φ hφ T c x y hxy k)

/-- The sheet label of the point above `y` after the `k`th chord is the next
root-orbit point. -/
theorem componentSheetRoot_orbitY
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    componentSheetRoot φ hφ T c y
        (componentChordOrbitY φ hφ T c x y hxy k) =
      componentChordOrbitRoot φ hφ T c x y hxy (k + 1) :=
  componentChordOrbitRoot_succ φ hφ T c x y hxy k

/-- The global branch section, obtained by using the coherently lifted copy in
the connected component of each target vertex. -/
noncomputable def branchVertex
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (v : γ) :
    F.vertexSet :=
  componentBranch φ hφ T (G.connectedComponentMk v) ⟨v, rfl⟩

@[simp]
theorem map_branchVertex
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (v : γ) :
    φ (branchVertex φ hφ T v) = v :=
  map_componentBranch φ hφ T (G.connectedComponentMk v) ⟨v, rfl⟩

/-- The branch section is injective because `φ` is its left inverse. -/
theorem branchVertex_injective
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) :
    Function.Injective (branchVertex φ hφ T) := by
  intro x y hxy
  simpa using congr_arg φ hxy

/-- The component-indexed and global presentations of a branch vertex agree. -/
theorem componentBranch_eq_branchVertex
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) :
    componentBranch φ hφ T c v =
      branchVertex φ hφ T v.1 := by
  rcases v with ⟨v, hv⟩
  subst c
  rfl

/-- Every edge of the chosen target forest has a corresponding direct source
edge between the coherently selected branch vertices. -/
theorem componentBranch_isLink
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    {x y : c.supp} (hxy : T.graph.Adj x.1 y.1) :
    ∃ e : F.edgeSet,
      F.IsLink e.1
        (componentBranch φ hφ T c x).1
        (componentBranch φ hφ T c y).1 := by
  rcases componentTargetPath_adj φ hφ T c hxy with hxyPath | hyxPath
  · have h :=
      liftPathStar_extend_nonempty φ hφ
        (FullSpanningForest.sourceRoot φ hφ c)
        (componentTargetPath φ hφ T c x)
        (componentTargetEdge φ hφ T c hxy)
    rw [← hxyPath] at h
    obtain ⟨e⟩ := h
    exact ⟨e.1, e.2⟩
  · have h :=
      liftPathStar_extend_nonempty φ hφ
        (FullSpanningForest.sourceRoot φ hφ c)
        (componentTargetPath φ hφ T c y)
        (componentTargetEdge φ hφ T c hxy.symm)
    rw [← hyxPath] at h
    obtain ⟨e⟩ := h
    exact ⟨e.1, e.2.symm⟩

/-- Global form of `componentBranch_isLink`: every chosen forest edge appears
directly between the global branch vertices. -/
theorem branchVertex_isLink
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) {x y : γ}
    (hxy : T.graph.Adj x y) :
    ∃ e : F.edgeSet,
      F.IsLink e.1
        (branchVertex φ hφ T x).1
        (branchVertex φ hφ T y).1 := by
  let c := G.connectedComponentMk x
  let x' : c.supp := ⟨x, rfl⟩
  have hyc : y ∈ c.supp :=
    (c.mem_supp_congr_adj (T.le_target hxy)).mp rfl
  let y' : c.supp := ⟨y, hyc⟩
  obtain ⟨e, he⟩ :=
    componentBranch_isLink φ hφ T c
      (x := x') (y := y') hxy
  rw [componentBranch_eq_branchVertex,
    componentBranch_eq_branchVertex] at he
  exact ⟨e, he⟩

/-- A compact package for the coherently lifted full spanning forest. -/
structure LiftedForestCopy
    {α β γ : Type*} (F : Graph α β) (G : SimpleGraph γ)
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) where
  branch : γ → F.vertexSet
  map_branch : ∀ v, φ (branch v) = v
  forestEdge : ∀ ⦃x y⦄, T.graph.Adj x y →
    ∃ e : F.edgeSet, F.IsLink e.1 (branch x).1 (branch y).1

/-- The lifted copy selected by the path-lifting construction above. -/
noncomputable def liftedForestCopy
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) :
    LiftedForestCopy F G φ hφ T where
  branch := branchVertex φ hφ T
  map_branch := map_branchVertex φ hφ T
  forestEdge := fun {_ _} hxy =>
    branchVertex_isLink φ hφ T hxy

/-- The selected branch vertices in one lifted target component. -/
def componentBranchSet
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent) :
    Set F.vertexSet :=
  Set.range (componentBranch φ hφ T c)

/-- The same branch set in the ambient source vertex type.  This is the
protected set passed to `collapseOutside`. -/
def componentBranchAmbientSet
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent) :
    Set α :=
  Set.range fun v : c.supp => (componentBranch φ hφ T c v).1

/-- The ambient protected set consisting of branch vertices from every target
component.  Outside contraction must use this global union. -/
def globalBranchAmbientSet
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) :
    Set α :=
  Set.range fun v : γ => (branchVertex φ hφ T v).1

theorem globalBranchAmbientSet_subset_vertexSet
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) :
    globalBranchAmbientSet φ hφ T ⊆ F.vertexSet := by
  rintro _ ⟨v, rfl⟩
  exact (branchVertex φ hφ T v).2

/-- A live source vertex belonging to the global branch set is exactly the
chosen branch vertex over its image. -/
theorem eq_branchVertex_of_mem_global
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (u : F.vertexSet)
    (hu : u.1 ∈ globalBranchAmbientSet φ hφ T) :
    u = branchVertex φ hφ T (φ u) := by
  obtain ⟨z, hz⟩ := hu
  have hzu : z = φ u := by
    calc
      z = φ (branchVertex φ hφ T z) :=
        (map_branchVertex φ hφ T z).symm
      _ = φ u := congr_arg φ (Subtype.ext hz)
  subst z
  exact Subtype.ext hz.symm

/-- Inside a fixed target component, membership in the selected global branch
copy is characterized by having the selected root-fibre sheet label. -/
theorem mem_global_iff_componentSheetRoot_eq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) (u : Fiber φ v.1) :
    u.1.1 ∈ globalBranchAmbientSet φ hφ T ↔
      componentSheetRoot φ hφ T c v u =
        componentRootFiber φ hφ c := by
  constructor
  · intro hu
    have hub :=
      eq_branchVertex_of_mem_global φ hφ T u.1 hu
    have hub' :
        u.1 = branchVertex φ hφ T v.1 := by
      simpa only [u.2] using hub
    have huc :
        u = componentBranchFiber φ hφ T c v := by
      apply Subtype.ext
      exact hub'.trans
        (componentBranch_eq_branchVertex φ hφ T c v).symm
    rw [huc, componentSheetRoot_branch]
  · intro hs
    let p := componentTargetPathPath φ hφ T c v
    have hu :
        u = pathTransport φ hφ p
          (componentRootFiber φ hφ c) := by
      calc
        u = pathTransport φ hφ p
            (componentSheetRoot φ hφ T c v u) := by
          change
            u = pathTransport φ hφ p
              (pathTransport φ hφ p.reverse u)
          simpa only [Quiver.Path.reverse_reverse] using
            (pathTransport_reverse_apply φ hφ p.reverse u).symm
        _ = pathTransport φ hφ p
            (componentRootFiber φ hφ c) :=
          congr_arg (pathTransport φ hφ p) hs
    have huc :
        u = componentBranchFiber φ hφ T c v := by
      rw [componentBranchFiber_eq_pathTransport]
      exact hu
    refine ⟨v.1, ?_⟩
    change
      (branchVertex φ hφ T v.1).1 = u.1.1
    rw [← componentBranch_eq_branchVertex φ hφ T c v]
    exact congr_arg (fun q : Fiber φ v.1 ↦ q.1.1) huc.symm

/-- The point above `x` in every strictly intermediate traversal is outside
the selected global forest copy. -/
theorem componentChordOrbitX_not_mem_global
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    {k : ℕ} (hk : 0 < k)
    (hlt : k < componentChordReturnTime φ hφ T c x y hxy) :
    (componentChordOrbitX φ hφ T c x y hxy k).1.1 ∉
      globalBranchAmbientSet φ hφ T := by
  rw [mem_global_iff_componentSheetRoot_eq]
  rw [componentSheetRoot_orbitX]
  exact componentChordOrbitRoot_ne_main
    φ hφ T c x y hxy hk hlt

/-- The point above `y` after every traversal whose successor is still
strictly before the return time lies outside the selected global forest copy. -/
theorem componentChordOrbitY_not_mem_global
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    {k : ℕ}
    (hlt : k + 1 < componentChordReturnTime φ hφ T c x y hxy) :
    (componentChordOrbitY φ hφ T c x y hxy k).1.1 ∉
      globalBranchAmbientSet φ hφ T := by
  rw [mem_global_iff_componentSheetRoot_eq]
  rw [componentSheetRoot_orbitY]
  exact componentChordOrbitRoot_ne_main
    φ hφ T c x y hxy (Nat.zero_lt_succ k) hlt

/-- The simple graph induced on source vertices outside the selected lifted
forest copy. -/
def componentOutsideGraph
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent) :
    SimpleGraph {u : F.vertexSet // u ∉ componentBranchSet φ hφ T c} :=
  F.nonloopShadow.induce {u | u ∉ componentBranchSet φ hφ T c}

/-- The two source edge copies selected by the perfect matching over a target
edge at its two branch endpoints. -/
structure BranchChordEnds
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) where
  uX : F.vertexSet
  uY : F.vertexSet
  eX : F.edgeSet
  eY : F.edgeSet
  linkX : F.IsLink eX.1
    (componentBranch φ hφ T c x).1 uX.1
  linkY : F.IsLink eY.1
    (componentBranch φ hφ T c y).1 uY.1
  map_uX : φ uX = y.1
  map_uY : φ uY = x.1

/-- Choose the two matching edges over an oriented target edge. -/
noncomputable def branchChordEnds
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    BranchChordEnds φ hφ T c x y := by
  let bx := componentBranch φ hφ T c x
  let branchY := componentBranch φ hφ T c y
  have hbx : φ bx = x.1 := by
    dsimp only [bx]
    exact map_componentBranch φ hφ T c x
  have hby : φ branchY = y.1 := by
    dsimp only [branchY]
    exact map_componentBranch φ hφ T c y
  let hx : Quiver.Star ((toPrefunctor φ).obj bx) :=
    ⟨y.1, ⟨by
      change G.Adj (φ bx) y.1
      rw [hbx]
      exact hxy⟩⟩
  let hy : Quiver.Star ((toPrefunctor φ).obj branchY) :=
    ⟨x.1, ⟨by
      change G.Adj (φ branchY) x.1
      rw [hby]
      exact hxy.symm⟩⟩
  let sx := Classical.choose ((star_bijective φ hφ bx).2 hx)
  have hsx : (toPrefunctor φ).star bx sx = hx :=
    Classical.choose_spec ((star_bijective φ hφ bx).2 hx)
  let sy := Classical.choose ((star_bijective φ hφ branchY).2 hy)
  have hsy : (toPrefunctor φ).star branchY sy = hy :=
    Classical.choose_spec ((star_bijective φ hφ branchY).2 hy)
  exact
    { uX := sx.1
      uY := sy.1
      eX := sx.2.1
      eY := sy.2.1
      linkX := sx.2.2
      linkY := sy.2.2
      map_uX := congr_arg Sigma.fst hsx
      map_uY := congr_arg Sigma.fst hsy }

/-- The boundary information obtained from the paper's detour path for one
target chord.

The second constructor is precisely the data that survives after all
non-branch vertices in one outside connected component are contracted. -/
inductive ChordBoundaryCertificate
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) : Type _ where
  | direct
      (e : F.edgeSet)
      (link : F.IsLink e.1
        (componentBranch φ hφ T c x).1
        (componentBranch φ hφ T c y).1)
  | throughOutside
      (uX uY : F.vertexSet)
      (eX eY : F.edgeSet)
      (edges_ne : eX ≠ eY)
      (linkX : F.IsLink eX.1
        (componentBranch φ hφ T c x).1 uX.1)
      (linkY : F.IsLink eY.1
        (componentBranch φ hφ T c y).1 uY.1)
      (map_uX : φ uX = y.1)
      (map_uY : φ uY = x.1)
      (connected :
        OutsideConnected F (globalBranchAmbientSet φ hφ T)
          uX.1 uY.1)

/-- If the two branch-incidence copies selected over a chord coincide, that
copy directly joins the two branch vertices.  Otherwise the copies are
distinct, as required for a later split-off. -/
theorem branchChordEnds_direct_or_edges_ne
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    (∃ e : F.edgeSet,
      F.IsLink e.1
        (componentBranch φ hφ T c x).1
        (componentBranch φ hφ T c y).1) ∨
      (branchChordEnds φ hφ T c x y hxy).eX ≠
        (branchChordEnds φ hφ T c x y hxy).eY := by
  let D := branchChordEnds φ hφ T c x y hxy
  by_cases hEdges : D.eX = D.eY
  · left
    have hxyCases :=
      D.linkX.eq_and_eq_or_eq_and_eq (hEdges ▸ D.linkY)
    rcases hxyCases with hsame | hcross
    · exfalso
      exact hxy.ne
        (by simpa using congr_arg φ (Subtype.ext hsame.1))
    · exact ⟨D.eX, hcross.2 ▸ D.linkX⟩
  · exact Or.inr hEdges

/-- In the non-direct case, the endpoint reached from the `x` branch lies
outside the globally selected forest copy. -/
theorem BranchChordEnds.uX_not_mem_global
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (D : BranchChordEnds φ hφ T c x y)
    (hne : D.eX ≠ D.eY) :
    D.uX.1 ∉ globalBranchAmbientSet φ hφ T := by
  rintro ⟨z, hz⟩
  have hbranch : branchVertex φ hφ T z = D.uX :=
    Subtype.ext hz
  have hzy : z = y.1 := by
    calc
      z = φ (branchVertex φ hφ T z) :=
        (map_branchVertex φ hφ T z).symm
      _ = φ D.uX := congr_arg φ hbranch
      _ = y.1 := D.map_uX
  subst z
  have huX :
      D.uX = componentBranch φ hφ T c y := by
    rw [componentBranch_eq_branchVertex]
    exact hbranch.symm
  have heX :
      F.IsLink D.eX.1
        (componentBranch φ hφ T c y).1
        (componentBranch φ hφ T c x).1 := by
    rw [← huX]
    exact D.linkX.symm
  have hmap :
      φ (componentBranch φ hφ T c x) = φ D.uY := by
    rw [map_componentBranch, D.map_uY]
  exact hne
    (sourceArrow_edge_eq_of_endpoint_image_eq φ hφ
      (componentBranch φ hφ T c y)
      (componentBranch φ hφ T c x) D.uY
      D.eX D.eY heX D.linkY hmap)

/-- In the non-direct case, the endpoint reached from the `y` branch lies
outside the globally selected forest copy. -/
theorem BranchChordEnds.uY_not_mem_global
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (D : BranchChordEnds φ hφ T c x y)
    (hne : D.eX ≠ D.eY) :
    D.uY.1 ∉ globalBranchAmbientSet φ hφ T := by
  rintro ⟨z, hz⟩
  have hbranch : branchVertex φ hφ T z = D.uY :=
    Subtype.ext hz
  have hzx : z = x.1 := by
    calc
      z = φ (branchVertex φ hφ T z) :=
        (map_branchVertex φ hφ T z).symm
      _ = φ D.uY := congr_arg φ hbranch
      _ = x.1 := D.map_uY
  subst z
  have huY :
      D.uY = componentBranch φ hφ T c x := by
    rw [componentBranch_eq_branchVertex]
    exact hbranch.symm
  have heY :
      F.IsLink D.eY.1
        (componentBranch φ hφ T c x).1
        (componentBranch φ hφ T c y).1 := by
    rw [← huY]
    exact D.linkY.symm
  have hmap :
      φ D.uX = φ (componentBranch φ hφ T c y) := by
    rw [D.map_uX, map_componentBranch]
  exact hne
    (sourceArrow_edge_eq_of_endpoint_image_eq φ hφ
      (componentBranch φ hφ T c x) D.uX
      (componentBranch φ hφ T c y)
      D.eX D.eY D.linkX heY hmap)

/-- A path-form witness from which a boundary certificate follows
immediately.  This isolates the graph-theoretic extraction from the covering
argument that constructs the detour. -/
structure ExteriorChordWalk
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) where
  uX : F.vertexSet
  uY : F.vertexSet
  eX : F.edgeSet
  eY : F.edgeSet
  edges_ne : eX ≠ eY
  linkX : F.IsLink eX.1
    (componentBranch φ hφ T c x).1 uX.1
  linkY : F.IsLink eY.1
    (componentBranch φ hφ T c y).1 uY.1
  map_uX : φ uX = y.1
  map_uY : φ uY = x.1
  middle :
    OutsideConnected F (globalBranchAmbientSet φ hφ T)
      uX.1 uY.1

/-- An exterior chord walk gives the exact boundary certificate needed after
contracting outside connected components. -/
noncomputable def ExteriorChordWalk.toBoundaryCertificate
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    {φ : MultigraphHom F G} {hφ : φ.HasPerfectFibers}
    {T : FullSpanningForest G} {c : G.ConnectedComponent}
    {x y : c.supp}
    (P : ExteriorChordWalk φ hφ T c x y) :
    ChordBoundaryCertificate φ hφ T c x y :=
  .throughOutside
    P.uX P.uY P.eX P.eY P.edges_ne
    P.linkX P.linkY P.map_uX P.map_uY P.middle

end MultigraphHom.Covering

end StrongRoberson
