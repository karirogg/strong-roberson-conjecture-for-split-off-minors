import StrongRoberson.Proof.ChordWalk
import StrongRoberson.Proof.CoveringReverse

/-!
# Chord endpoints at the first monodromy return

This file specializes the generic endpoint comparisons from `ChordWalk` to
the last traversal before the least positive return of the fundamental-loop
monodromy.  Keeping the specialization separate avoids coupling the
covering-orbit arithmetic to the construction of the exterior walk.
-/

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- The target chord, viewed as a star based at the actual source point
reached over `x` in traversal `k`. -/
noncomputable def componentChordOrbitTargetStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    Quiver.Star
      ((toPrefunctor φ).obj
        (componentChordOrbitX φ hφ T c x y hxy k).1) :=
  ⟨y.1, ⟨by
    change G.Adj
      (φ (componentChordOrbitX φ hφ T c x y hxy k).1) y.1
    rw [(componentChordOrbitX φ hφ T c x y hxy k).2]
    exact hxy⟩⟩

/-- The canonical one-arrow source lift of the chord during traversal `k`. -/
noncomputable def componentChordOrbitLiftStar
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    Quiver.Star
      (componentChordOrbitX φ hφ T c x y hxy k).1 :=
  liftStar φ hφ
    (componentChordOrbitX φ hφ T c x y hxy k).1
    (componentChordOrbitTargetStar φ hφ T c x y hxy k)

/-- The endpoint of the canonical one-arrow chord lift lies over `y`. -/
@[simp]
theorem map_componentChordOrbitLiftStar_fst
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) (k : ℕ) :
    φ (componentChordOrbitLiftStar φ hφ T c x y hxy k).1 =
      y.1 := by
  exact congr_arg Sigma.fst
    (map_liftStar φ hφ
      (componentChordOrbitX φ hφ T c x y hxy k).1
      (componentChordOrbitTargetStar φ hφ T c x y hxy k))

/-- The `x`-side edge selected by `branchChordEnds` is exactly the edge copy
in the canonical one-arrow chord lift at traversal zero. -/
theorem branchChordEnds_eX_eq_orbitLiftStar_zero
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    (branchChordEnds φ hφ T c x y hxy).eX =
      (componentChordOrbitLiftStar φ hφ T c x y hxy 0).2.1 := by
  let D := branchChordEnds φ hφ T c x y hxy
  let X0 := componentChordOrbitX φ hφ T c x y hxy 0
  let S0 := componentChordOrbitLiftStar φ hφ T c x y hxy 0
  have hX0 :
      X0 = componentBranchFiber φ hφ T c x :=
    componentChordOrbitX_zero φ hφ T c x y hxy
  have hX0v :
      X0.1 = componentBranch φ hφ T c x := by
    exact congr_arg Subtype.val hX0
  have hS0 :
      F.IsLink S0.2.1.1
        (componentBranch φ hφ T c x).1 S0.1.1 := by
    rw [← hX0v]
    exact S0.2.2
  have hmap :
      φ D.uX = φ S0.1 := by
    exact D.map_uX.trans
      (map_componentChordOrbitLiftStar_fst
        φ hφ T c x y hxy 0).symm
  exact sourceArrow_edge_eq_of_endpoint_image_eq φ hφ
    (componentBranch φ hφ T c x) D.uX S0.1
    D.eX S0.2.1 D.linkX hS0 hmap

/-- The `y`-point reached by the last chord traversal before the least
positive return is the selected branch point above `y`. -/
theorem componentChordOrbitY_pred_return_eq_branch
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    componentChordOrbitY φ hφ T c x y hxy
        (componentChordReturnTime φ hφ T c x y hxy - 1) =
      componentBranchFiber φ hφ T c y := by
  let r := componentChordReturnTime φ hφ T c x y hxy
  have hr : 1 ≤ r :=
    componentChordReturnTime_pos φ hφ T c x y hxy
  have hpred : (r - 1) + 1 = r :=
    Nat.sub_add_cancel hr
  apply eq_componentBranchFiber_of_componentSheetRoot_eq
    φ hφ T c y
  rw [componentSheetRoot_orbitY, hpred]
  exact componentChordReturnTime_apply φ hφ T c x y hxy

/-- The endpoint selected from the `y` branch by `branchChordEnds` is the
`x`-point at the start of the last traversal before the least return. -/
theorem branchChordEnds_uY_eq_orbitX_pred_return
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    (branchChordEnds φ hφ T c x y hxy).uY =
      (componentChordOrbitX φ hφ T c x y hxy
        (componentChordReturnTime φ hφ T c x y hxy - 1)).1 := by
  exact branchChordEnds_uY_eq_orbitX_of_orbitY_eq_branch
    φ hφ T c x y hxy
    (componentChordReturnTime φ hφ T c x y hxy - 1)
    (componentChordOrbitY_pred_return_eq_branch
      φ hφ T c x y hxy)

/-- The `y`-side edge selected by `branchChordEnds` is the same underlying
edge copy as the canonical chord lift in the last traversal before return.
Its orientation in `branchChordEnds` is the reverse orientation, from the
selected `y` branch back to that traversal's point over `x`. -/
theorem branchChordEnds_eY_eq_orbitLiftStar_pred_return
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.vertexSet] [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    (branchChordEnds φ hφ T c x y hxy).eY =
      (componentChordOrbitLiftStar φ hφ T c x y hxy
        (componentChordReturnTime φ hφ T c x y hxy - 1)).2.1 := by
  let D := branchChordEnds φ hφ T c x y hxy
  let k := componentChordReturnTime φ hφ T c x y hxy - 1
  let Xk := componentChordOrbitX φ hφ T c x y hxy k
  let Sk := componentChordOrbitLiftStar φ hφ T c x y hxy k
  have huY :
      D.uY = Xk.1 := by
    exact branchChordEnds_uY_eq_orbitX_pred_return
      φ hφ T c x y hxy
  have heY :
      F.IsLink D.eY.1 Xk.1.1
        (componentBranch φ hφ T c y).1 := by
    rw [← huY]
    exact D.linkY.symm
  have hmap :
      φ (componentBranch φ hφ T c y) = φ Sk.1 := by
    exact (map_componentBranch φ hφ T c y).trans
      (map_componentChordOrbitLiftStar_fst
        φ hφ T c x y hxy k).symm
  exact sourceArrow_edge_eq_of_endpoint_image_eq φ hφ
    Xk.1 (componentBranch φ hφ T c y) Sk.1
    D.eY Sk.2.1 heY Sk.2.2 hmap

/-- Distinct boundary edge copies force the fundamental-loop return orbit to
contain at least two traversals.  If the least return were one, the two
boundary copies would be links between the same pair of branch vertices and
therefore would coincide. -/
theorem two_le_componentChordReturnTime_of_branchChordEnds_edges_ne
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
  let r := componentChordReturnTime φ hφ T c x y hxy
  have hr : 0 < r :=
    componentChordReturnTime_pos φ hφ T c x y hxy
  by_contra hnot
  have hrle : r ≤ 1 := by omega
  have hrone : r = 1 := by omega
  have hrone' :
      componentChordReturnTime φ hφ T c x y hxy = 1 := by
    simpa only [r] using hrone
  have huY :
      D.uY = componentBranch φ hφ T c x := by
    have h :=
      branchChordEnds_uY_eq_orbitX_pred_return
        φ hφ T c x y hxy
    rw [hrone'] at h
    simp only [Nat.reduceSubDiff] at h
    have h' :
        D.uY =
          (componentChordOrbitX φ hφ T c x y hxy 0).1 := by
      simpa only [D] using h
    exact h'.trans
      (congr_arg Subtype.val
        (componentChordOrbitX_zero φ hφ T c x y hxy))
  apply hne
  have heY :
      F.IsLink D.eY.1
        (componentBranch φ hφ T c x).1
        (componentBranch φ hφ T c y).1 := by
    rw [← huY]
    exact D.linkY.symm
  have hmap :
      φ D.uX = φ (componentBranch φ hφ T c y) := by
    rw [D.map_uX, map_componentBranch]
  exact sourceArrow_edge_eq_of_endpoint_image_eq φ hφ
    (componentBranch φ hφ T c x) D.uX
    (componentBranch φ hφ T c y)
    D.eX D.eY D.linkX heY hmap

end MultigraphHom.Covering

end StrongRoberson
