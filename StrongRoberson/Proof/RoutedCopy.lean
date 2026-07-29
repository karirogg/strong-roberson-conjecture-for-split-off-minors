import StrongRoberson.Proof.RouteSplitting
import StrongRoberson.Proof.SubgraphCopy

/-!
# Turning edge-disjoint short routes into a represented copy

This file packages the last, purely operational, part of the paper proof.
Suppose that every live edge copy of a finite graph `H` has been routed in
`F`, either by one edge copy or by two edge copies, and that different source
edges use disjoint sets of edge copies.  Splitting all two-edge routes then
leaves an exact `SubgraphCopy` of `H`.

The route data is deliberately indexed by `H.edgeSet`: parallel source edges
remain different indices, and the disjointness hypothesis concerns concrete
edge identities in `F`.
-/

namespace StrongRoberson

universe u

/-- Two endpoint descriptions of one concrete edge remain the same unordered
pair after applying any vertex map.  This small helper is useful when route
disjointness is inferred from the image of a source edge under a homomorphism.
-/
theorem image_sym2_eq_of_isLink_of_isLink
    {α β γ : Type u} {H : Graph α β}
    {e : β} {x y z w : α}
    (f : α → γ) (hxy : H.IsLink e x y) (hzw : H.IsLink e z w) :
    s(f x, f y) = s(f z, f w) := by
  rcases hxy.eq_and_eq_or_eq_and_eq hzw with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    exact Sym2.eq_swap

/-- A route of length one or two between two specified ambient vertices. -/
inductive ShortEdgeRoute {γ δ : Type u} (F : Graph γ δ) (x y : γ) where
  | direct (edge : δ) (isLink : F.IsLink edge x y)
  | lengthTwo (firstEdge secondEdge : δ) (middle : γ)
      (first_isLink : F.IsLink firstEdge x middle)
      (second_isLink : F.IsLink secondEdge middle y)
      (edges_ne : firstEdge ≠ secondEdge)

namespace ShortEdgeRoute

variable {γ δ : Type u} {F : Graph γ δ} {x y : γ}

/-- The edge identity retained as the represented edge after all splitting. -/
def firstEdge : ShortEdgeRoute F x y → δ
  | .direct e _ => e
  | .lengthTwo e _ _ _ _ _ => e

/-- Whether a concrete ambient edge identity occurs in a route. -/
def Uses : ShortEdgeRoute F x y → δ → Prop
  | .direct e _, f => f = e
  | .lengthTwo e₁ e₂ _ _ _ _, f => f = e₁ ∨ f = e₂

@[simp]
theorem uses_firstEdge (r : ShortEdgeRoute F x y) :
    r.Uses r.firstEdge := by
  cases r <;> simp [Uses, firstEdge]

/-- The proposition that a short route genuinely has length two. -/
def IsLengthTwo : ShortEdgeRoute F x y → Prop
  | .direct _ _ => False
  | .lengthTwo _ _ _ _ _ _ => True

/-- A total accessor for the second edge.  On direct routes it repeats the
first edge; the value is used only under an `IsLengthTwo` hypothesis. -/
def secondEdge : ShortEdgeRoute F x y → δ
  | .direct e _ => e
  | .lengthTwo _ e _ _ _ _ => e

/-- A total accessor for the middle vertex.  On direct routes it is the left
endpoint; the value is used only under an `IsLengthTwo` hypothesis. -/
def middle : ShortEdgeRoute F x y → γ
  | .direct _ _ => x
  | .lengthTwo _ _ z _ _ _ => z

theorem first_isLink_of_isLengthTwo
    (r : ShortEdgeRoute F x y) (h : r.IsLengthTwo) :
    F.IsLink r.firstEdge x r.middle := by
  cases r with
  | direct e he => simp [IsLengthTwo] at h
  | lengthTwo e₁ e₂ z h₁ h₂ hne =>
      exact h₁

theorem second_isLink_of_isLengthTwo
    (r : ShortEdgeRoute F x y) (h : r.IsLengthTwo) :
    F.IsLink r.secondEdge r.middle y := by
  cases r with
  | direct e he => simp [IsLengthTwo] at h
  | lengthTwo e₁ e₂ z h₁ h₂ hne =>
      exact h₂

theorem edges_ne_of_isLengthTwo
    (r : ShortEdgeRoute F x y) (h : r.IsLengthTwo) :
    r.firstEdge ≠ r.secondEdge := by
  cases r with
  | direct e he => simp [IsLengthTwo] at h
  | lengthTwo e₁ e₂ z h₁ h₂ hne =>
      exact hne

theorem uses_secondEdge_of_isLengthTwo
    (r : ShortEdgeRoute F x y) (h : r.IsLengthTwo) :
    r.Uses r.secondEdge := by
  cases r with
  | direct e he => simp [IsLengthTwo] at h
  | lengthTwo e₁ e₂ z h₁ h₂ hne =>
      simp [Uses, secondEdge]

theorem direct_isLink_of_not_isLengthTwo
    (r : ShortEdgeRoute F x y) (h : ¬ r.IsLengthTwo) :
    F.IsLink r.firstEdge x y := by
  cases r with
  | direct e he => exact he
  | lengthTwo e₁ e₂ z h₁ h₂ hne =>
      exact (h (by simp [IsLengthTwo])).elim

end ShortEdgeRoute

/-- A route certificate for one concrete live edge copy of `H`.

The chosen orientation `left`--`right` is harmless because `Graph.IsLink` is
symmetric.  Keeping it in the data makes construction of length-two routes
convenient for later lifting arguments.
-/
structure RoutedEdge {α β γ δ : Type u}
    (H : Graph α β) (F : Graph γ δ)
    (branch : H.vertexSet ↪ F.vertexSet) (e : H.edgeSet) where
  left : H.vertexSet
  right : H.vertexSet
  source_isLink : H.IsLink e.1 left.1 right.1
  route :
    ShortEdgeRoute F (branch left).1 (branch right).1

/-- An exact branch-vertex embedding together with pairwise edge-disjoint
short routes for all live source edge copies. -/
structure RoutedCopy {α β γ δ : Type u}
    (H : Graph α β) (F : Graph γ δ) where
  branch : H.vertexSet ↪ F.vertexSet
  edgeRoute : ∀ e : H.edgeSet, RoutedEdge H F branch e
  routes_disjoint :
    ∀ {e f : H.edgeSet}, e ≠ f →
      ∀ {d : δ},
        (edgeRoute e).route.Uses d →
        ¬ (edgeRoute f).route.Uses d

namespace RoutedCopy

variable {α β γ δ : Type u} {H : Graph α β} {F : Graph γ δ}

/-- The live source edges whose chosen routes have length two. -/
def longEdges (c : RoutedCopy H F) :=
  {e : H.edgeSet // (c.edgeRoute e).route.IsLengthTwo}

instance [Finite β] (c : RoutedCopy H F) : Finite c.longEdges :=
  by
    unfold longEdges
    infer_instance

/-- The family of length-two routes extracted from a routed copy. -/
def lengthTwoRoutes (c : RoutedCopy H F) :
    EdgeDisjointLengthTwoRoutes F c.longEdges where
  firstEdge i := (c.edgeRoute i.1).route.firstEdge
  secondEdge i := (c.edgeRoute i.1).route.secondEdge
  left i := (c.branch (c.edgeRoute i.1).left).1
  middle i := (c.edgeRoute i.1).route.middle
  right i := (c.branch (c.edgeRoute i.1).right).1
  first_isLink i :=
    (c.edgeRoute i.1).route.first_isLink_of_isLengthTwo i.2
  second_isLink i :=
    (c.edgeRoute i.1).route.second_isLink_of_isLengthTwo i.2
  edges_ne i :=
    (c.edgeRoute i.1).route.edges_ne_of_isLengthTwo i.2
  pairwise_disjoint := by
    intro i j hij
    have hij' : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Subtype.ext h
    exact
      ⟨fun h ↦ c.routes_disjoint hij'
          (c.edgeRoute i.1).route.uses_firstEdge
          (h ▸ (c.edgeRoute j.1).route.uses_firstEdge),
        fun h ↦ c.routes_disjoint hij'
          (c.edgeRoute i.1).route.uses_firstEdge
          (h ▸
            (c.edgeRoute j.1).route.uses_secondEdge_of_isLengthTwo j.2),
        fun h ↦ c.routes_disjoint hij'
          ((c.edgeRoute i.1).route.uses_secondEdge_of_isLengthTwo i.2)
          (h ▸ (c.edgeRoute j.1).route.uses_firstEdge),
        fun h ↦ c.routes_disjoint hij'
          ((c.edgeRoute i.1).route.uses_secondEdge_of_isLengthTwo i.2)
          (h ▸
            (c.edgeRoute j.1).route.uses_secondEdge_of_isLengthTwo j.2)⟩

/-- The concrete edge identity used to represent a source edge after all
length-two routes have been split. -/
def representedEdge (c : RoutedCopy H F) (e : H.edgeSet) : δ :=
  (c.edgeRoute e).route.firstEdge

theorem representedEdge_injective (c : RoutedCopy H F) :
    Function.Injective c.representedEdge := by
  intro e f hef
  by_contra hne
  apply c.routes_disjoint hne
    (c.edgeRoute e).route.uses_firstEdge
  change
    (c.edgeRoute e).route.firstEdge =
      (c.edgeRoute f).route.firstEdge at hef
  rw [hef]
  exact (c.edgeRoute f).route.uses_firstEdge

/-- After simultaneously splitting all long routes, the retained first edge
of every route directly links the two corresponding branch vertices. -/
theorem representedEdge_isLink_after_split [Finite β]
    (c : RoutedCopy H F) (e : H.edgeSet) :
    ((c.lengthTwoRoutes).splitAll.graph).IsLink
      (c.representedEdge e)
      (c.branch (c.edgeRoute e).left).1
      (c.branch (c.edgeRoute e).right).1 := by
  classical
  by_cases hlong : (c.edgeRoute e).route.IsLengthTwo
  · let i : c.longEdges := ⟨e, hlong⟩
    exact (c.lengthTwoRoutes.splitAll.route_isLink i)
  · apply c.lengthTwoRoutes.splitAll.untouched_isLink
      ((c.edgeRoute e).route.direct_isLink_of_not_isLengthTwo hlong)
    intro i
    have hei : e ≠ i.1 := by
      intro h
      subst e
      exact hlong i.2
    constructor
    · intro h
      exact c.routes_disjoint hei
        (c.edgeRoute e).route.uses_firstEdge
        (h ▸ (c.edgeRoute i.1).route.uses_firstEdge)
    · intro h
      exact c.routes_disjoint hei
        (c.edgeRoute e).route.uses_firstEdge
        (h ▸
          (c.edgeRoute i.1).route.uses_secondEdge_of_isLengthTwo i.2)

/-- The exact represented copy obtained after all long routes are split. -/
noncomputable def subgraphCopyAfterSplit [Finite β]
    (c : RoutedCopy H F) :
    SubgraphCopy H (c.lengthTwoRoutes.splitAll.graph) := by
  classical
  let K := c.lengthTwoRoutes.splitAll.graph
  let b : H.vertexSet ↪ K.vertexSet :=
    { toFun := fun x ↦
        ⟨(c.branch x).1, by
          rw [c.lengthTwoRoutes.splitAll.vertexSet_eq]
          exact (c.branch x).2⟩
      inj' := by
        intro x y h
        apply c.branch.injective
        apply Subtype.ext
        exact congrArg (fun z : K.vertexSet ↦ z.1) h }
  let q : H.edgeSet ↪ K.edgeSet :=
    { toFun := fun e ↦
        ⟨c.representedEdge e,
          (c.representedEdge_isLink_after_split e).edge_mem⟩
      inj' := by
        intro e f h
        apply c.representedEdge_injective
        exact congrArg Subtype.val h }
  exact
    { vertexEmbedding := b
      edgeEmbedding := q
      map_isLink := by
        intro e x y
        have hH := (c.edgeRoute e).source_isLink
        have hK := c.representedEdge_isLink_after_split e
        constructor
        · intro hxy
          rcases hH.eq_and_eq_or_eq_and_eq hxy with h | h
          · rcases h with ⟨hxl, hyr⟩
            have hxl' : (c.edgeRoute e).left = x :=
              Subtype.ext hxl
            have hyr' : (c.edgeRoute e).right = y :=
              Subtype.ext hyr
            subst x
            subst y
            exact hK
          · rcases h with ⟨hxr, hyl⟩
            have hxr' : (c.edgeRoute e).left = y :=
              Subtype.ext hxr
            have hyl' : (c.edgeRoute e).right = x :=
              Subtype.ext hyl
            subst x
            subst y
            exact hK.symm
        · intro hxy
          rcases hK.eq_and_eq_or_eq_and_eq hxy with h | h
          · have hxl : (c.edgeRoute e).left = x := by
              apply c.branch.injective
              apply Subtype.ext
              exact h.1
            have hyr : (c.edgeRoute e).right = y := by
              apply c.branch.injective
              apply Subtype.ext
              exact h.2
            subst x
            subst y
            exact hH
          · have hly : (c.edgeRoute e).left = y := by
              apply c.branch.injective
              apply Subtype.ext
              exact h.1
            have hrx : (c.edgeRoute e).right = x := by
              apply c.branch.injective
              apply Subtype.ext
              exact h.2
            subst x
            subst y
            exact hH.symm }

/-- The generic routed-copy assembly theorem. -/
theorem isSplitOffMinor [Finite β] (c : RoutedCopy H F) :
    IsSplitOffMinor H F :=
  IsSplitOffMinor.trans c.subgraphCopyAfterSplit.isSplitOffMinor
    c.lengthTwoRoutes.splitAll.isSplitOffMinor

end RoutedCopy

end StrongRoberson
