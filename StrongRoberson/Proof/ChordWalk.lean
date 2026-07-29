import StrongRoberson.Proof.LiftForest
import StrongRoberson.Proof.LoopSplice
import StrongRoberson.Proof.CoveringReversePath
import StrongRoberson.Proof.CoveringOneArrow
import StrongRoberson.Proof.ForestAvoidance

/-!
# Exterior walks for target chords

This file carries out the fundamental-cycle part of the lift argument.  The
chosen forest copy and the finite root-fibre orbit are defined in
`LiftForest`; here they are assembled into the path outside that copy.
-/

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- Every traversal of the target chord is represented by one concrete source
edge between the corresponding orbit points. -/
theorem componentChordOrbit_isLink
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    ∃ e : F.edgeSet,
      F.IsLink e.1
        (componentChordOrbitX φ hφ T c x y hxy k).1.1
        (componentChordOrbitY φ hφ T c x y hxy k).1.1 := by
  simpa [componentChordOrbitY] using
    (exists_isLink_pathTransport_toPathAt φ hφ
      (targetChordArrow hxy)
      (componentChordOrbitX φ hφ T c x y hxy k))

/-- Two avoiding lifted forest segments give the bridge from the point after
the `k`th chord to the point before the next chord. -/
theorem componentChordOrbit_bridge_of_avoids
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ)
    (hy :
      SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
        (transportedPath φ hφ
          (componentTargetPathPath φ hφ T c y).reverse
          (componentChordOrbitY φ hφ T c x y hxy k)))
    (hx :
      SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
        (transportedPath φ hφ
          (componentTargetPathPath φ hφ T c x)
          (componentChordOrbitRoot φ hφ T c x y hxy (k + 1)))) :
    OutsideConnected F (globalBranchAmbientSet φ hφ T)
      (componentChordOrbitY φ hφ T c x y hxy k).1.1
      (componentChordOrbitX φ hφ T c x y hxy (k + 1)).1.1 := by
  have hyConn := hy.toOutsideConnected
  have hxConn := hx.toOutsideConnected
  have hroot :=
    componentChordOrbitRoot_succ φ hφ T c x y hxy k
  rw [hroot] at hyConn
  exact OutsideConnected.trans hyConn
    (by simpa [componentChordOrbitX] using hxConn)

/-- Every strictly pre-return orbit step has an outside bridge, obtained by
lifting the reverse `y` forest path and then the forward `x` forest path on
the same non-selected sheet. -/
theorem componentChordOrbit_bridge
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ)
    (hbound :
      k + 1 < componentChordReturnTime φ hφ T c x y hxy) :
    OutsideConnected F (globalBranchAmbientSet φ hφ T)
      (componentChordOrbitY φ hφ T c x y hxy k).1.1
      (componentChordOrbitX φ hφ T c x y hxy (k + 1)).1.1 := by
  have hroot :
      componentChordOrbitRoot φ hφ T c x y hxy (k + 1) ≠
        componentRootFiber φ hφ c :=
    componentChordOrbitRoot_ne_main
      φ hφ T c x y hxy (Nat.zero_lt_succ k) hbound
  have hx :=
    componentForestPath_avoids_of_root_ne
      φ hφ T c x
      (componentChordOrbitRoot φ hφ T c x y hxy (k + 1))
      hroot
  have hsheet :
      componentSheetRoot φ hφ T c y
          (componentChordOrbitY φ hφ T c x y hxy k) ≠
        componentRootFiber φ hφ c := by
    intro hs
    apply hroot
    exact
      (componentSheetRoot_orbitY
        φ hφ T c x y hxy k).symm.trans hs
  have hy :=
    componentForestPath_reverse_avoids_of_sheetRoot_ne
      φ hφ T c y
      (componentChordOrbitY φ hφ T c x y hxy k)
      hsheet
  exact componentChordOrbit_bridge_of_avoids
    φ hφ T c x y hxy k hy hx

/-- Concatenate successive outside bridges and intermediate chord edges.

This is a recursive presentation of the other side of the lifted fundamental
cycle.  It is equivalent to lifting a repeated fundamental-loop path, while
avoiding the dependent endpoint casts of one large concatenation. -/
theorem componentChordOrbit_chain
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    (m : ℕ)
    (hbridge : ∀ k : ℕ,
      k + 1 < componentChordReturnTime φ hφ T c x y hxy →
      OutsideConnected F (globalBranchAmbientSet φ hφ T)
        (componentChordOrbitY φ hφ T c x y hxy k).1.1
        (componentChordOrbitX φ hφ T c x y hxy (k + 1)).1.1)
    (hbound :
      m + 1 < componentChordReturnTime φ hφ T c x y hxy) :
    OutsideConnected F (globalBranchAmbientSet φ hφ T)
      (componentChordOrbitY φ hφ T c x y hxy 0).1.1
      (componentChordOrbitX φ hφ T c x y hxy (m + 1)).1.1 := by
  induction m with
  | zero =>
      simpa using hbridge 0 hbound
  | succ m ih =>
      have hprev :
          m + 1 < componentChordReturnTime φ hφ T c x y hxy := by
        omega
      have hnext :
          (m + 1) + 1 <
            componentChordReturnTime φ hφ T c x y hxy := by
        omega
      have hc :=
        componentChordOrbit_isLink φ hφ T c x y hxy (m + 1)
      obtain ⟨e, he⟩ := hc
      have htoY :
          OutsideConnected F (globalBranchAmbientSet φ hφ T)
            (componentChordOrbitY φ hφ T c x y hxy 0).1.1
            (componentChordOrbitY φ hφ T c x y hxy (m + 1)).1.1 :=
        .tail (ih hprev) he
          (componentChordOrbitY_not_mem_global
            φ hφ T c x y hxy hnext)
      have hb := hbridge (m + 1) hnext
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        OutsideConnected.trans htoY hb

/-- The first source endpoint reached by the chord is the zeroth `y`-orbit
point. -/
theorem branchChordEnds_uX_eq_orbitY_zero
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    (branchChordEnds φ hφ T c x y hxy).uX =
      (componentChordOrbitY φ hφ T c x y hxy 0).1 := by
  let D := branchChordEnds φ hφ T c x y hxy
  let X0 := componentChordOrbitX φ hφ T c x y hxy 0
  let Y0 := componentChordOrbitY φ hφ T c x y hxy 0
  obtain ⟨e, he⟩ :=
    exists_isLink_pathTransport_toPathAt φ hφ
      (targetChordArrow hxy) X0
  have hX0 :
      X0 = componentBranchFiber φ hφ T c x :=
    componentChordOrbitX_zero φ hφ T c x y hxy
  have hY0 :
      Y0 =
        pathTransport φ hφ (targetChordArrow hxy).toPath
          (componentBranchFiber φ hφ T c x) := by
    dsimp only [Y0, componentChordOrbitY]
    exact congr_arg
      (pathTransport φ hφ (targetChordArrow hxy).toPath) hX0
  have he' :
      F.IsLink e.1
        (componentBranch φ hφ T c x).1 Y0.1.1 := by
    rw [hX0] at he
    rw [hY0]
    simpa [componentBranchFiber] using he
  have hmap : φ D.uX = φ Y0.1 :=
    D.map_uX.trans Y0.2.symm
  have hedges : D.eX = e :=
    sourceArrow_edge_eq_of_endpoint_image_eq φ hφ
      (componentBranch φ hφ T c x) D.uX Y0.1
      D.eX e D.linkX he' hmap
  apply Subtype.ext
  exact D.linkX.right_unique (hedges ▸ he')

/-- A fibre point whose backwards forest transport is the selected root is
the selected branch point in that fibre. -/
theorem eq_componentBranchFiber_of_componentSheetRoot_eq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) (u : Fiber φ v.1)
    (hu :
      componentSheetRoot φ hφ T c v u =
        componentRootFiber φ hφ c) :
    u = componentBranchFiber φ hφ T c v := by
  let p := componentTargetPathPath φ hφ T c v
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
      congr_arg (pathTransport φ hφ p) hu
    _ = componentBranchFiber φ hφ T c v :=
      (componentBranchFiber_eq_pathTransport φ hφ T c v).symm

/-- If a chord traversal ends at the selected `y` branch, then its initial
point above `x` is the endpoint chosen from the `y` branch by
`branchChordEnds`. -/
theorem branchChordEnds_uY_eq_orbitX_of_orbitY_eq_branch
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ)
    (hY :
      componentChordOrbitY φ hφ T c x y hxy k =
        componentBranchFiber φ hφ T c y) :
    (branchChordEnds φ hφ T c x y hxy).uY =
      (componentChordOrbitX φ hφ T c x y hxy k).1 := by
  let D := branchChordEnds φ hφ T c x y hxy
  let Xk := componentChordOrbitX φ hφ T c x y hxy k
  let Yk := componentChordOrbitY φ hφ T c x y hxy k
  obtain ⟨e, he⟩ :=
    exists_isLink_pathTransport_toPathAt φ hφ
      (targetChordArrow hxy) Xk
  have heOrbit :
      F.IsLink e.1 Xk.1.1 Yk.1.1 := by
    simpa [Xk, Yk, componentChordOrbitY] using he
  have hYk :
      Yk = componentBranchFiber φ hφ T c y :=
    hY
  have he' :
      F.IsLink e.1
        (componentBranch φ hφ T c y).1 Xk.1.1 := by
    rw [hYk] at heOrbit
    simpa [componentBranchFiber] using heOrbit.symm
  have hmap : φ D.uY = φ Xk.1 :=
    D.map_uY.trans Xk.2.symm
  have hedges : D.eY = e :=
    sourceArrow_edge_eq_of_endpoint_image_eq φ hφ
      (componentBranch φ hφ T c y) D.uY Xk.1
      D.eY e D.linkY he' hmap
  apply Subtype.ext
  exact D.linkY.right_unique (hedges ▸ he')

/-- Immediately before the least return, the chord traversal ends at the
selected `y` branch. -/
theorem componentChordLastY_eq_branch
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    componentChordOrbitY φ hφ T c x y hxy
        (componentChordReturnTime φ hφ T c x y hxy - 1) =
      componentBranchFiber φ hφ T c y := by
  apply eq_componentBranchFiber_of_componentSheetRoot_eq
  rw [componentSheetRoot_orbitY]
  have hn :
      componentChordReturnTime φ hφ T c x y hxy - 1 + 1 =
        componentChordReturnTime φ hφ T c x y hxy :=
    Nat.sub_add_cancel
      (componentChordReturnTime_pos φ hφ T c x y hxy)
  rw [hn, componentChordOrbitRoot_return]

/-- The endpoint chosen from the `y` branch is the `x`-orbit point
immediately preceding the least return. -/
theorem branchChordEnds_uY_eq_orbitX_last
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    (branchChordEnds φ hφ T c x y hxy).uY =
      (componentChordOrbitX φ hφ T c x y hxy
        (componentChordReturnTime φ hφ T c x y hxy - 1)).1 :=
  branchChordEnds_uY_eq_orbitX_of_orbitY_eq_branch
    φ hφ T c x y hxy
    (componentChordReturnTime φ hφ T c x y hxy - 1)
    (componentChordLastY_eq_branch φ hφ T c x y hxy)

/-- In the non-direct case, the least monodromy return uses at least two
fundamental-loop traversals. -/
theorem two_le_componentChordReturnTime_of_edges_ne
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    (hne :
      (branchChordEnds φ hφ T c x y hxy).eX ≠
        (branchChordEnds φ hφ T c x y hxy).eY) :
    2 ≤ componentChordReturnTime φ hφ T c x y hxy := by
  let D := branchChordEnds φ hφ T c x y hxy
  let n := componentChordReturnTime φ hφ T c x y hxy
  by_contra hnTwo
  have hnPos : 0 < n :=
    componentChordReturnTime_pos φ hφ T c x y hxy
  have hn : n = 1 := by omega
  have huY :
      D.uY = componentBranch φ hφ T c x := by
    calc
      D.uY =
          (componentChordOrbitX φ hφ T c x y hxy (n - 1)).1 := by
        exact branchChordEnds_uY_eq_orbitX_last
          φ hφ T c x y hxy
      _ = (componentChordOrbitX φ hφ T c x y hxy 0).1 := by
        rw [hn]
      _ = componentBranch φ hφ T c x := by
        exact congr_arg Subtype.val
          (componentChordOrbitX_zero φ hφ T c x y hxy)
  apply (BranchChordEnds.uY_not_mem_global φ hφ T c x y D hne)
  refine ⟨x.1, ?_⟩
  change
    (branchVertex φ hφ T x.1).1 = D.uY.1
  rw [← componentBranch_eq_branchVertex φ hφ T c x, huY]

/-- The orbit-chain construction, once supplied with its successive outside
bridges, connects exactly the two non-branch endpoints selected for a chord. -/
theorem branchChordEnds_middle_of_bridges
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    (hne :
      (branchChordEnds φ hφ T c x y hxy).eX ≠
        (branchChordEnds φ hφ T c x y hxy).eY)
    (hbridge : ∀ k : ℕ,
      k + 1 < componentChordReturnTime φ hφ T c x y hxy →
      OutsideConnected F (globalBranchAmbientSet φ hφ T)
        (componentChordOrbitY φ hφ T c x y hxy k).1.1
        (componentChordOrbitX φ hφ T c x y hxy (k + 1)).1.1) :
    OutsideConnected F (globalBranchAmbientSet φ hφ T)
      (branchChordEnds φ hφ T c x y hxy).uX.1
      (branchChordEnds φ hφ T c x y hxy).uY.1 := by
  let n := componentChordReturnTime φ hφ T c x y hxy
  have hnTwo : 2 ≤ n :=
    two_le_componentChordReturnTime_of_edges_ne
      φ hφ T c x y hxy hne
  have hbound : (n - 2) + 1 < n := by omega
  have hchain :=
    componentChordOrbit_chain φ hφ T c x y hxy
      (n - 2) hbridge hbound
  have hindex : n - 2 + 1 = n - 1 := by omega
  rw [hindex] at hchain
  rw [branchChordEnds_uX_eq_orbitY_zero φ hφ T c x y hxy,
    branchChordEnds_uY_eq_orbitX_last φ hφ T c x y hxy]
  exact hchain

/-- Successive outside bridges supply a boundary certificate for the chord. -/
theorem nonempty_chordBoundaryCertificate_of_bridges
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    (hbridge : ∀ k : ℕ,
      k + 1 < componentChordReturnTime φ hφ T c x y hxy →
      OutsideConnected F (globalBranchAmbientSet φ hφ T)
        (componentChordOrbitY φ hφ T c x y hxy k).1.1
        (componentChordOrbitX φ hφ T c x y hxy (k + 1)).1.1) :
    Nonempty (ChordBoundaryCertificate φ hφ T c x y) := by
  rcases branchChordEnds_direct_or_edges_ne
      φ hφ T c x y hxy with ⟨e, he⟩ | hne
  · exact ⟨.direct e he⟩
  · let D := branchChordEnds φ hφ T c x y hxy
    exact ⟨.throughOutside
      D.uX D.uY D.eX D.eY hne
      D.linkX D.linkY D.map_uX D.map_uY
      (branchChordEnds_middle_of_bridges
        φ hφ T c x y hxy hne hbridge)⟩

/-- Chosen boundary certificate obtained from the orbit bridges. -/
noncomputable def chordBoundaryCertificate_of_bridges
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    (hbridge : ∀ k : ℕ,
      k + 1 < componentChordReturnTime φ hφ T c x y hxy →
      OutsideConnected F (globalBranchAmbientSet φ hφ T)
        (componentChordOrbitY φ hφ T c x y hxy k).1.1
        (componentChordOrbitX φ hφ T c x y hxy (k + 1)).1.1) :
    ChordBoundaryCertificate φ hφ T c x y :=
  Classical.choice
    (nonempty_chordBoundaryCertificate_of_bridges
      φ hφ T c x y hxy hbridge)

/-- The paper's fundamental-cycle construction gives the boundary certificate
for every target edge outside the chosen spanning forest. -/
noncomputable def chordBoundaryCertificate
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1)
    (_hnotT : ¬ T.graph.Adj x.1 y.1) :
    ChordBoundaryCertificate φ hφ T c x y :=
  chordBoundaryCertificate_of_bridges φ hφ T c x y hxy
    (fun k hbound ↦
      componentChordOrbit_bridge
        φ hφ T c x y hxy k hbound)

end MultigraphHom.Covering

end StrongRoberson
