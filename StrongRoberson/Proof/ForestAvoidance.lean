import StrongRoberson.Proof.CoveringOneArrow
import StrongRoberson.Proof.CoveringReverse
import StrongRoberson.Proof.CoveringReversePath
import StrongRoberson.Proof.OutsidePath

/-!
# Avoidance on non-selected forest sheets

The chosen lift of the spanning forest is one sheet of the covering above
that forest.  A lift of a chosen root-to-vertex forest path which begins on
any other root-fibre point therefore never meets the chosen sheet.

This file isolates that invariant from the fundamental-cycle construction.
-/

namespace StrongRoberson

namespace MultigraphHom.Covering

/-- Heterogeneously equal quiver paths have the same length. -/
theorem path_length_eq_of_heq
    {U : Type*} [Quiver U]
    {a b a' b' : U}
    {p : Quiver.Path a b} {q : Quiver.Path a' b'}
    (ha : a = a') (hb : b = b')
    (hpq : p ≍ q) :
    p.length = q.length := by
  subst a'
  subst b'
  exact congrArg Quiver.Path.length (eq_of_heq hpq)

/-- Mapping a quiver path through a prefunctor preserves its length. -/
@[simp]
theorem Prefunctor.mapPath_length
    {U V : Type*} [Quiver U] [Quiver V]
    (ψ : U ⥤q V) {a b : U} (p : Quiver.Path a b) :
    (ψ.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      simp only [Prefunctor.mapPath_cons, Quiver.Path.length_cons, ih]

/-- A one-arrow source path avoids a set as soon as its two endpoints do.

The length formulation is useful for a lifted path whose sole arrow is known
from its image rather than exposed definitionally. -/
theorem SourcePath.Avoids.of_length_one
    {α β : Type*} {F : Graph α β} {B : Set α}
    {u v : F.vertexSet} (p : Quiver.Path u v)
    (hlen : p.length = 1)
    (hu : u.1 ∉ B) (hv : v.1 ∉ B) :
    SourcePath.Avoids B p := by
  cases p with
  | nil => simp at hlen
  | @cons w _ p e =>
      have hp0 : p.length = 0 := by
        exact Nat.add_right_cancel
          (show p.length + 1 = 0 + 1 by
            simpa only [Quiver.Path.length_cons, Nat.zero_add] using hlen)
      have huw : u = w := Quiver.Path.eq_of_length_zero p hp0
      subst w
      have hpNil : p = Quiver.Path.nil :=
        Quiver.Path.eq_nil_of_length_zero p hp0
      subst p
      exact ⟨hu, hv⟩

/-- The lift of a single target arrow has exactly one source arrow. -/
theorem transportedPath_length_toPath
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x y : γ}
    (e : (show Target G from x) ⟶ (show Target G from y))
    (u : Fiber φ x) :
    (transportedPath φ hφ e.toPath u).length = 1 := by
  have hmap :=
    map_liftPath_path φ hφ u.1
      (targetPathAt φ e.toPath u)
  have htarget := targetPathAt_heq φ e.toPath u
  have hlenMap :
      ((toPrefunctor φ).mapPath
        (transportedPath φ hφ e.toPath u)).length =
        (targetPathAt φ e.toPath u).length :=
    path_length_eq_of_heq rfl
      (pathTransport φ hφ e.toPath u).2 hmap
  have hlenTarget :
      (targetPathAt φ e.toPath u).length =
        e.toPath.length :=
    path_length_eq_of_heq u.2 rfl htarget
  simpa only [Prefunctor.mapPath_length,
    Quiver.Path.length_toPath] using hlenMap.trans hlenTarget

/-- The lifted source path over an empty target path is itself empty, up to
the endpoint equality inherent in fibre transport. -/
theorem transportedPath_nil_heq
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    {x : γ} (u : Fiber φ x) :
    transportedPath φ hφ
        (Quiver.Path.nil :
          Quiver.Path (show Target G from x) (show Target G from x))
        u ≍
      (Quiver.Path.nil : Quiver.Path u.1 u.1) := by
  rcases u with ⟨u, hu⟩
  subst x
  exact
    (Sigma.mk.inj_iff.mp
      (liftPathStar_map φ hφ u
        (show Quiver.PathStar u from
          ⟨u, Quiver.Path.nil⟩))).2

/-- Transporting an off-sheet root point to the endpoint of any simple
rooted forest walk cannot land in the globally selected branch copy. -/
theorem pathTransport_forestWalk_not_mem_global
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp)
    (p : T.graph.Walk
      (componentRootTarget (γ := γ) φ hφ c) v.1)
    (hp : p.IsPath)
    (r : Fiber φ (componentRootTarget (γ := γ) φ hφ c))
    (hr : r ≠ componentRootFiber φ hφ c) :
    (pathTransport φ hφ
      (walkToPath G (p.mapLe T.le_target)) r).1.1 ∉
        globalBranchAmbientSet φ hφ T := by
  intro hmem
  have hpEq :
      (⟨p, hp⟩ :
        T.graph.Path
          (componentRootTarget (γ := γ) φ hφ c) v.1) =
        FullSpanningForest.componentPath φ hφ T c v :=
    T.isAcyclic.path_unique _ _
  have hpVal :
      p = (FullSpanningForest.componentPath φ hφ T c v).1 :=
    congrArg Subtype.val hpEq
  subst p
  let q := componentTargetPathPath φ hφ T c v
  let u : Fiber φ v.1 := pathTransport φ hφ q r
  have huMem :
      u.1.1 ∈ globalBranchAmbientSet φ hφ T := by
    change
      (pathTransport φ hφ q r).1.1 ∈
        globalBranchAmbientSet φ hφ T at hmem
    exact hmem
  have hsheet :
      componentSheetRoot φ hφ T c v u =
        componentRootFiber φ hφ c :=
    (mem_global_iff_componentSheetRoot_eq φ hφ T c v u).mp huMem
  have hback :
      componentSheetRoot φ hφ T c v u = r := by
    exact pathTransport_reverse_apply φ hφ q r
  exact hr (hback.symm.trans hsheet)

/-- Every vertex of the lift of a simple rooted forest walk remains outside
the selected global branch copy when its initial root-fibre point is not the
selected one. -/
theorem transportedForestWalk_avoids_of_root_ne
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    {z : γ} (hz : z ∈ c.supp)
    (p : T.graph.Walk
      (componentRootTarget (γ := γ) φ hφ c) z)
    (hp : p.IsPath)
    (r : Fiber φ (componentRootTarget (γ := γ) φ hφ c))
    (hr : r ≠ componentRootFiber φ hφ c) :
    SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
      (transportedPath φ hφ
        (walkToPath G (p.mapLe T.le_target)) r) := by
  let root := componentRootTarget (γ := γ) φ hφ c
  let motive :
      ∀ (a b : γ), T.graph.Walk a b → Prop :=
    fun a b q ↦
      ∀ (ha : a = root) (hb : b ∈ c.supp) (hq : q.IsPath),
        SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
          (transportedPath φ hφ
            (walkToPath G
              (((q.copy ha rfl) :
                T.graph.Walk root b).mapLe T.le_target)) r)
  have hnil :
      ∀ {a : γ}, motive a a SimpleGraph.Walk.nil := by
    intro a ha hb hp
    cases ha
    have hrOutside :
        r.1.1 ∉ globalBranchAmbientSet φ hφ T := by
      have h :=
        pathTransport_forestWalk_not_mem_global
          φ hφ T c ⟨root, hb⟩
          SimpleGraph.Walk.nil (by simp) r hr
      change
        (pathTransport φ hφ
          (Quiver.Path.nil :
            Quiver.Path (show Target G from root)
              (show Target G from root)) r).1.1 ∉
            globalBranchAmbientSet φ hφ T at h
      rw [pathTransport_nil] at h
      exact h
    have hAvoidNil :
        SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
          (Quiver.Path.nil : Quiver.Path r.1 r.1) :=
      SourcePath.Avoids.nil hrOutside
    change
      SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
        (transportedPath φ hφ
          (Quiver.Path.nil :
            Quiver.Path (show Target G from root)
              (show Target G from root)) r)
    exact hAvoidNil.of_heq rfl
      (congrArg Subtype.val (pathTransport_nil φ hφ r)).symm
      (transportedPath_nil_heq φ hφ r).symm
  have hconcat :
      ∀ {a b d : γ} (q₀ : T.graph.Walk a b)
        (h : T.graph.Adj b d),
        motive a b q₀ → motive a d (q₀.concat h) := by
    intro a b d q₀ h ih ha hd hp
    cases ha
    have hpParts := (SimpleGraph.Walk.concat_isPath_iff h).mp hp
    have hb : b ∈ c.supp :=
      (c.mem_supp_congr_adj (T.le_target h)).mpr hd
    have hprefix := ih rfl hb hpParts.1
    let q :=
      walkToPath G (q₀.mapLe T.le_target)
    let e :
        (show Target G from b) ⟶
          (show Target G from d) :=
      ⟨T.le_target h⟩
    let s : Fiber φ b :=
      pathTransport φ hφ q r
    have htarget :
        walkToPath G
            ((q₀.concat h).mapLe T.le_target) =
          q.comp e.toPath := by
      rw [walk_mapLe_concat, walkToPath_concat]
    have hend :
        (pathTransport φ hφ e.toPath s).1.1 ∉
          globalBranchAmbientSet φ hφ T := by
      have hfull :=
        pathTransport_forestWalk_not_mem_global
          φ hφ T c ⟨d, hd⟩ (q₀.concat h) hp r hr
      rw [htarget, pathTransport_comp] at hfull
      exact hfull
    have hlast :
        SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
          (transportedPath φ hφ e.toPath s) :=
      SourcePath.Avoids.of_length_one
        (transportedPath φ hφ e.toPath s)
        (transportedPath_length_toPath φ hφ e s)
        hprefix.end_not_mem hend
    have hcomp :
        SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
          ((transportedPath φ hφ q r).comp
            (transportedPath φ hφ e.toPath s)) :=
      hprefix.comp hlast
    have hpaths :
        transportedPath φ hφ (q.comp e.toPath) r ≍
          (transportedPath φ hφ q r).comp
            (transportedPath φ hφ e.toPath s) :=
      transportedPath_comp φ hφ q e.toPath r
    change
      SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
        (transportedPath φ hφ
          (walkToPath G
            ((q₀.concat h).mapLe T.le_target)) r)
    rw [htarget]
    exact hcomp.of_heq rfl
        (congrArg Subtype.val
          (pathTransport_comp φ hφ q e.toPath r)).symm
        hpaths.symm
  exact
    SimpleGraph.Walk.concatRec
      (motive := motive) hnil hconcat p rfl hz hp

/-- The lifted chosen root-to-`v` forest path stays entirely outside the
global branch copy on every non-selected root sheet. -/
theorem componentForestPath_avoids_of_root_ne
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp)
    (r : Fiber φ (componentRootTarget (γ := γ) φ hφ c))
    (hr : r ≠ componentRootFiber φ hφ c) :
    SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
      (transportedPath φ hφ
        (componentTargetPathPath φ hφ T c v) r) := by
  change
    SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
      (transportedPath φ hφ
        (walkToPath G
          ((FullSpanningForest.componentPath φ hφ T c v).1.mapLe
            T.le_target)) r)
  exact
    transportedForestWalk_avoids_of_root_ne
      φ hφ T c v.2
      (FullSpanningForest.componentPath φ hφ T c v).1
      (FullSpanningForest.componentPath φ hφ T c v).2
      r hr

/-- Reverse form of `componentForestPath_avoids_of_root_ne`: a point above
`v` whose root-sheet label is not the selected root lifts the reversed chosen
forest path without meeting the global branch copy. -/
theorem componentForestPath_reverse_avoids_of_sheetRoot_ne
    {α β γ : Type*} {F : Graph α β} {G : SimpleGraph γ}
    [Finite F.edgeSet]
    (φ : MultigraphHom F G) (hφ : φ.HasPerfectFibers)
    (T : FullSpanningForest G) (c : G.ConnectedComponent)
    (v : c.supp) (u : Fiber φ v.1)
    (hu :
      componentSheetRoot φ hφ T c v u ≠
        componentRootFiber φ hφ c) :
    SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
      (transportedPath φ hφ
        (componentTargetPathPath φ hφ T c v).reverse u) := by
  let p := componentTargetPathPath φ hφ T c v
  let r : Fiber φ (componentRootTarget (γ := γ) φ hφ c) :=
    componentSheetRoot φ hφ T c v u
  have hr :
      r ≠ componentRootFiber φ hφ c :=
    hu
  have hforward :
      SourcePath.Avoids (globalBranchAmbientSet φ hφ T)
        (transportedPath φ hφ p r) :=
    componentForestPath_avoids_of_root_ne
      φ hφ T c v r hr
  have hreturn :
      pathTransport φ hφ p r = u := by
    simpa only [r, componentSheetRoot, p,
      Quiver.Path.reverse_reverse] using
        pathTransport_reverse_apply φ hφ p.reverse u
  have hpaths :
      transportedPath φ hφ p.reverse u ≍
        (transportedPath φ hφ p r).reverse :=
    (transportedPath_heq_of_fiber_eq
      φ hφ p.reverse hreturn.symm).trans
        (transportedPath_reverse φ hφ p r)
  exact hforward.reverse.of_heq
    (congrArg Subtype.val hreturn) rfl hpaths.symm

end MultigraphHom.Covering

end StrongRoberson
