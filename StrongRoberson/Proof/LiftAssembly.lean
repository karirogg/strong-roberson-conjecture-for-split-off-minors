import StrongRoberson.Proof.LiftForest
import StrongRoberson.Proof.CollapseOutside
import StrongRoberson.Proof.RoutedCopy

/-!
# Conditional assembly of the perfect-fibre lift

This file contains all global bookkeeping after the fundamental-cycle
argument.  Its sole graph-theoretic input is a `ChordBoundaryProvider`,
supplying the certificate isolated in `LiftForest.lean` for each target edge
outside a chosen full spanning forest.

All non-branch source vertices are contracted globally.  Forest edges and
direct chord certificates survive as one-edge routes; exterior chord
certificates become two-edge routes because their outside endpoints acquire
the same representative.  Concrete source edge identities are retained, and
their target images prove disjointness of routes belonging to distinct target
edges.
-/

namespace StrongRoberson

universe u

namespace MultigraphHom.Covering

/-- Endpoint descriptions of one live source edge have the same unordered
image pair under a map defined on live vertices. -/
theorem live_image_sym2_eq_of_isLink_of_isLink
    {α β γ : Type u} {F : Graph α β}
    (f : F.vertexSet → γ) {d : β}
    {u v u' v' : F.vertexSet}
    (huv : F.IsLink d u.1 v.1)
    (huv' : F.IsLink d u'.1 v'.1) :
    s(f u, f v) = s(f u', f v') := by
  rcases huv.eq_and_eq_or_eq_and_eq huv' with h | h
  · have hu : u = u' := Subtype.ext h.1
    have hv : v = v' := Subtype.ext h.2
    rw [hu, hv]
  · have hu : u = v' := Subtype.ext h.1
    have hv : v = u' := Subtype.ext h.2
    rw [hu, hv]
    exact Sym2.eq_swap

variable {α β γ : Type u} {F : Graph α β} {G : SimpleGraph γ}
  [Finite F.edgeSet]

/-- The exact unresolved input to the conditional lift assembly: every target
adjacency not selected by `T` has the boundary certificate extracted by the
paper's fundamental-cycle argument. -/
abbrev ChordBoundaryProvider
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) :=
  ∀ (c : G.ConnectedComponent) (x y : c.supp),
    G.Adj x.1 y.1 →
    ¬ T.graph.Adj x.1 y.1 →
    ChordBoundaryCertificate φ hφ T c x y

/-- Globally contract every non-loop edge whose two endpoints lie outside the
coherently selected branch section. -/
noncomputable def collapsedAlongBranches
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) :
    CollapseOutsideResult F (globalBranchAmbientSet φ hφ T) :=
  CollapseOutsideResult.collapseOutside F
    (globalBranchAmbientSet φ hφ T)
    (globalBranchAmbientSet_subset_vertexSet φ hφ T)

/-- The branch section, viewed as an embedding into the globally collapsed
graph.  This includes isolated target vertices; their survival follows from
the protected-set invariant rather than from incidence with a route. -/
noncomputable def collapsedBranchEmbedding
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) :
    (simpleToMultiGraph G).vertexSet ↪
      (collapsedAlongBranches φ hφ T).graph.vertexSet where
  toFun v :=
    ⟨(branchVertex φ hφ T v.1).1,
      (collapsedAlongBranches φ hφ T).protected_mem
        ⟨v.1, rfl⟩⟩
  inj' := by
    intro x y hxy
    have hbranch :
        branchVertex φ hφ T x.1 =
          branchVertex φ hφ T y.1 := by
      apply Subtype.ext
      exact congrArg
        (fun z :
          (collapsedAlongBranches φ hφ T).graph.vertexSet ↦ z.1)
        hxy
    exact Subtype.ext (branchVertex_injective φ hφ T hbranch)

/-- A routed target edge together with the original source-link witness for
every ambient edge copy it uses.  The latter field is what makes global
edge-copy disjointness independent of endpoint choices. -/
structure CollapsedRouteData
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G)
    (e : (simpleToMultiGraph G).edgeSet)
    extends
      RoutedEdge (simpleToMultiGraph G)
        (collapsedAlongBranches φ hφ T).graph
        (collapsedBranchEmbedding φ hφ T) e where
  used_source_link :
    ∀ {d : β}, toRoutedEdge.route.Uses d →
      ∃ u v : F.vertexSet,
        F.IsLink d u.1 v.1 ∧ e.1 = s(φ u, φ v)

/-- Construct the collapsed short route for one concrete target edge. -/
noncomputable def collapsedRouteData
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G)
    (provide : ChordBoundaryProvider φ hφ T)
    (e : (simpleToMultiGraph G).edgeSet) :
    CollapsedRouteData φ hφ T e := by
  classical
  let C := collapsedAlongBranches φ hφ T
  let hex :=
    (simpleToMultiGraph G).exists_isLink_of_mem_edgeSet e.2
  let x := Classical.choose hex
  let y := Classical.choose (Classical.choose_spec hex)
  have hxy :
      (simpleToMultiGraph G).IsLink e.1 x y :=
    Classical.choose_spec (Classical.choose_spec hex)
  let x' : (simpleToMultiGraph G).vertexSet :=
    ⟨x, hxy.left_mem⟩
  let y' : (simpleToMultiGraph G).vertexSet :=
    ⟨y, hxy.right_mem⟩
  by_cases hforest : T.graph.Adj x y
  · let hdex := branchVertex_isLink φ hφ T hforest
    let d := Classical.choose hdex
    have hd : F.IsLink d.1
        (branchVertex φ hφ T x).1
        (branchVertex φ hφ T y).1 :=
      Classical.choose_spec hdex
    have hxB :
        (branchVertex φ hφ T x).1 ∈
          globalBranchAmbientSet φ hφ T :=
      ⟨x, rfl⟩
    have hyB :
        (branchVertex φ hφ T y).1 ∈
          globalBranchAmbientSet φ hφ T :=
      ⟨y, rfl⟩
    have hdC : C.graph.IsLink d.1
        (branchVertex φ hφ T x).1
        (branchVertex φ hφ T y).1 := by
      have hs := C.boundary_isLink hxB hd
      rw [C.protected_fixed hyB] at hs
      exact hs
    refine
      { left := x'
        right := y'
        source_isLink := hxy
        route := .direct d.1 hdC
        used_source_link := ?_ }
    intro q hq
    change q = d.1 at hq
    subst q
    refine
      ⟨branchVertex φ hφ T x,
        branchVertex φ hφ T y, hd, ?_⟩
    simpa only [map_branchVertex] using hxy.1
  · let c := G.connectedComponentMk x
    let xc : c.supp := ⟨x, rfl⟩
    have hyc : y ∈ c.supp :=
      (c.mem_supp_congr_adj hxy.2).mp rfl
    let yc : c.supp := ⟨y, hyc⟩
    have cert := provide c xc yc hxy.2 hforest
    cases cert with
    | direct d hd =>
        have hd' : F.IsLink d.1
            (branchVertex φ hφ T x).1
            (branchVertex φ hφ T y).1 := by
          simpa only [componentBranch_eq_branchVertex] using hd
        have hxB :
            (branchVertex φ hφ T x).1 ∈
              globalBranchAmbientSet φ hφ T :=
          ⟨x, rfl⟩
        have hyB :
            (branchVertex φ hφ T y).1 ∈
              globalBranchAmbientSet φ hφ T :=
          ⟨y, rfl⟩
        have hdC : C.graph.IsLink d.1
            (branchVertex φ hφ T x).1
            (branchVertex φ hφ T y).1 := by
          have hs := C.boundary_isLink hxB hd'
          rw [C.protected_fixed hyB] at hs
          exact hs
        refine
          { left := x'
            right := y'
            source_isLink := hxy
            route := .direct d.1 hdC
            used_source_link := ?_ }
        intro q hq
        change q = d.1 at hq
        subst q
        refine
          ⟨componentBranch φ hφ T c xc,
            componentBranch φ hφ T c yc, hd, ?_⟩
        simpa only [map_componentBranch] using hxy.1
    | throughOutside uX uY eX eY hedges hX hY
        mapX mapY connected =>
        have hX' : F.IsLink eX.1
            (branchVertex φ hφ T x).1 uX.1 := by
          simpa only [componentBranch_eq_branchVertex] using hX
        have hY' : F.IsLink eY.1
            (branchVertex φ hφ T y).1 uY.1 := by
          simpa only [componentBranch_eq_branchVertex] using hY
        have hxB :
            (branchVertex φ hφ T x).1 ∈
              globalBranchAmbientSet φ hφ T :=
          ⟨x, rfl⟩
        have hyB :
            (branchVertex φ hφ T y).1 ∈
              globalBranchAmbientSet φ hφ T :=
          ⟨y, rfl⟩
        have hfirst : C.graph.IsLink eX.1
            (branchVertex φ hφ T x).1
            (C.representative uX.1) :=
          C.boundary_isLink hxB hX'
        have hrep :
            C.representative uX.1 =
              C.representative uY.1 :=
          C.outsideConnected_representative_eq connected
        have hsecond : C.graph.IsLink eY.1
            (C.representative uX.1)
            (branchVertex φ hφ T y).1 := by
          have hs := (C.boundary_isLink hyB hY').symm
          rw [← hrep] at hs
          exact hs
        have hedges' : eX.1 ≠ eY.1 := by
          intro h
          exact hedges (Subtype.ext h)
        refine
          { left := x'
            right := y'
            source_isLink := hxy
            route :=
              .lengthTwo eX.1 eY.1
                (C.representative uX.1)
                hfirst hsecond hedges'
            used_source_link := ?_ }
        intro q hq
        change q = eX.1 ∨ q = eY.1 at hq
        rcases hq with hq | hq
        · subst q
          refine
            ⟨componentBranch φ hφ T c xc, uX, hX, ?_⟩
          simpa only [map_componentBranch, mapX] using hxy.1
        · subst q
          refine
            ⟨componentBranch φ hφ T c yc, uY, hY, ?_⟩
          calc
            e.1 = s(x, y) := hxy.1
            _ = s(y, x) := Sym2.eq_swap
            _ = s(φ (componentBranch φ hφ T c yc), φ uY) := by
              rw [map_componentBranch, mapY]

/-- All collapsed target routes, packaged with their common branch embedding
and their concrete edge-copy disjointness proof. -/
noncomputable def collapsedRoutedCopy
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G)
    (provide : ChordBoundaryProvider φ hφ T) :
    RoutedCopy (simpleToMultiGraph G)
      (collapsedAlongBranches φ hφ T).graph where
  branch := collapsedBranchEmbedding φ hφ T
  edgeRoute e :=
    (collapsedRouteData φ hφ T provide e).toRoutedEdge
  routes_disjoint := by
    intro e f hef d hde hdf
    let De := collapsedRouteData φ hφ T provide e
    let Df := collapsedRouteData φ hφ T provide f
    have hde' : De.toRoutedEdge.route.Uses d := by
      exact hde
    have hdf' : Df.toRoutedEdge.route.Uses d := by
      exact hdf
    obtain ⟨u, v, huv, he⟩ := De.used_source_link hde'
    obtain ⟨u', v', huv', hf⟩ := Df.used_source_link hdf'
    apply hef
    apply Subtype.ext
    exact he.trans
      ((live_image_sym2_eq_of_isLink_of_isLink φ huv huv').trans
        hf.symm)

/-- Conditional perfect-fibre lift for an explicitly supplied full spanning
forest.  The only missing mathematical input is `provide`. -/
theorem isSplitOffMinor_of_chordBoundaryProvider
    [Finite γ]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G)
    (provide : ChordBoundaryProvider φ hφ T) :
    IsSplitOffMinor (simpleToMultiGraph G) F :=
  IsSplitOffMinor.trans
    (collapsedRoutedCopy φ hφ T provide).isSplitOffMinor
    (collapsedAlongBranches φ hφ T).isSplitOffMinor

/-- Conditional perfect-fibre lift using the canonical chosen full spanning
forest.  This is the form intended for the final theorem once the chord
provider has been discharged. -/
theorem perfectFibers_implies_splitOffMinor_of_chordBoundaryProvider
    [Finite γ]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (provide :
      ChordBoundaryProvider φ hφ (FullSpanningForest.choose G)) :
    IsSplitOffMinor (simpleToMultiGraph G) F :=
  isSplitOffMinor_of_chordBoundaryProvider
    φ hφ (FullSpanningForest.choose G) provide

end MultigraphHom.Covering

end StrongRoberson
