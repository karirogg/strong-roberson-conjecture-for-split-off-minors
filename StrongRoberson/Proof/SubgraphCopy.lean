import StrongRoberson.Proof.Operations

/-!
# Certified copies inside an edge-typed graph

The final step of the paper proof identifies a represented copy of the target
graph inside the graph produced by the lifting argument.  This file packages
that step without requiring the two graphs to use the same ambient vertex or
edge types.

Crucially, vertices and edge *copies* are embedded separately.  Thus distinct
parallel edges of the source remain distinct in the represented copy even
when they have the same endpoints.
-/

namespace StrongRoberson

universe u

/-- A copy of `H` represented inside `F`.

Both embeddings are defined on the live subtypes.  `map_isLink` is exact, not
merely forward-preserving: after applying the two embeddings, an edge copy has
precisely the same pair of endpoints as it had in `H`.
-/
structure SubgraphCopy {α β γ δ : Type u}
    (H : Graph α β) (F : Graph γ δ) where
  vertexEmbedding : H.vertexSet ↪ F.vertexSet
  edgeEmbedding : H.edgeSet ↪ F.edgeSet
  map_isLink : ∀ (e : H.edgeSet) (x y : H.vertexSet),
    H.IsLink e.1 x.1 y.1 ↔
      F.IsLink (edgeEmbedding e).1
        (vertexEmbedding x).1 (vertexEmbedding y).1

namespace SubgraphCopy

variable {α β γ δ : Type u} {H : Graph α β} {F : Graph γ δ}

/-- The ambient vertices used by a represented copy. -/
def vertexImage (c : SubgraphCopy H F) : Set γ :=
  Set.range (fun x ↦ (c.vertexEmbedding x).1)

/-- The ambient edge copies used by a represented copy. -/
def edgeImage (c : SubgraphCopy H F) : Set δ :=
  Set.range (fun e ↦ (c.edgeEmbedding e).1)

/-- The actual image graph: first retain exactly the represented edge copies,
then retain exactly the represented vertices. -/
def imageGraph (c : SubgraphCopy H F) : Graph γ δ :=
  (F.restrict c.edgeImage).induce c.vertexImage

@[simp]
theorem vertexSet_imageGraph (c : SubgraphCopy H F) :
    c.imageGraph.vertexSet = c.vertexImage :=
  rfl

@[simp]
theorem isLink_imageGraph (c : SubgraphCopy H F)
    (e : δ) (x y : γ) :
    c.imageGraph.IsLink e x y ↔
      (e ∈ c.edgeImage ∧ F.IsLink e x y) ∧
        x ∈ c.vertexImage ∧ y ∈ c.vertexImage :=
  Iff.rfl

/-- The image graph really is a subgraph of the ambient graph. -/
theorem imageGraph_le (c : SubgraphCopy H F) :
    c.imageGraph ≤ F := by
  apply le_trans (Graph.induce_le ?_) Graph.restrict_le
  rintro x ⟨v, rfl⟩
  exact (c.vertexEmbedding v).2

/-- Send a live source vertex to the corresponding live image vertex. -/
def vertexToImage (c : SubgraphCopy H F) (x : H.vertexSet) :
    c.imageGraph.vertexSet :=
  ⟨(c.vertexEmbedding x).1, ⟨x, rfl⟩⟩

theorem vertexToImage_injective (c : SubgraphCopy H F) :
    Function.Injective c.vertexToImage := by
  intro x y hxy
  apply c.vertexEmbedding.injective
  apply Subtype.ext
  exact congrArg (fun z : c.imageGraph.vertexSet ↦ z.1) hxy

theorem vertexToImage_surjective (c : SubgraphCopy H F) :
    Function.Surjective c.vertexToImage := by
  intro x
  have hx := x.2
  change x.1 ∈ c.vertexImage at hx
  rcases hx with ⟨v, hv⟩
  exact ⟨v, Subtype.ext hv⟩

/-- The source live vertices are equivalent to the live image vertices. -/
noncomputable def vertexEquiv (c : SubgraphCopy H F) :
    H.vertexSet ≃ c.imageGraph.vertexSet :=
  Equiv.ofBijective c.vertexToImage
    ⟨c.vertexToImage_injective, c.vertexToImage_surjective⟩

@[simp]
theorem vertexEquiv_apply (c : SubgraphCopy H F) (x : H.vertexSet) :
    c.vertexEquiv x = c.vertexToImage x :=
  rfl

/-- Every embedded live source edge is live in the image graph. -/
theorem edgeEmbedding_mem_imageGraph (c : SubgraphCopy H F)
    (e : H.edgeSet) :
    (c.edgeEmbedding e).1 ∈ c.imageGraph.edgeSet := by
  obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet e.2
  let x' : H.vertexSet := ⟨x, hxy.left_mem⟩
  let y' : H.vertexSet := ⟨y, hxy.right_mem⟩
  have hF : F.IsLink (c.edgeEmbedding e).1
      (c.vertexEmbedding x').1 (c.vertexEmbedding y').1 := by
    exact (c.map_isLink e x' y').mp hxy
  have hK : c.imageGraph.IsLink (c.edgeEmbedding e).1
      (c.vertexEmbedding x').1 (c.vertexEmbedding y').1 := by
    rw [isLink_imageGraph]
    exact ⟨⟨⟨e, rfl⟩, hF⟩, ⟨x', rfl⟩, ⟨y', rfl⟩⟩
  exact hK.edge_mem

@[simp]
theorem edgeSet_imageGraph (c : SubgraphCopy H F) :
    c.imageGraph.edgeSet = c.edgeImage := by
  ext e
  constructor
  · intro he
    obtain ⟨x, y, hxy⟩ :=
      c.imageGraph.exists_isLink_of_mem_edgeSet he
    exact ((c.isLink_imageGraph e x y).mp hxy).1.1
  · rintro ⟨f, rfl⟩
    exact c.edgeEmbedding_mem_imageGraph f

/-- Send a live source edge copy to the corresponding live image edge copy. -/
def edgeToImage (c : SubgraphCopy H F) (e : H.edgeSet) :
    c.imageGraph.edgeSet :=
  ⟨(c.edgeEmbedding e).1, c.edgeEmbedding_mem_imageGraph e⟩

theorem edgeToImage_injective (c : SubgraphCopy H F) :
    Function.Injective c.edgeToImage := by
  intro e f hef
  apply c.edgeEmbedding.injective
  apply Subtype.ext
  exact congrArg (fun z : c.imageGraph.edgeSet ↦ z.1) hef

theorem edgeToImage_surjective (c : SubgraphCopy H F) :
    Function.Surjective c.edgeToImage := by
  intro e
  obtain ⟨x, y, hxy⟩ :=
    c.imageGraph.exists_isLink_of_mem_edgeSet e.2
  have he : e.1 ∈ c.edgeImage :=
    ((c.isLink_imageGraph e.1 x y).mp hxy).1.1
  rcases he with ⟨f, hf⟩
  exact ⟨f, Subtype.ext hf⟩

/-- The source live edge copies are equivalent to the live image edge copies.
This equivalence, rather than an endpoint-based edge encoding, is what keeps
parallel edge identities distinct. -/
noncomputable def edgeEquiv (c : SubgraphCopy H F) :
    H.edgeSet ≃ c.imageGraph.edgeSet :=
  Equiv.ofBijective c.edgeToImage
    ⟨c.edgeToImage_injective, c.edgeToImage_surjective⟩

@[simp]
theorem edgeEquiv_apply (c : SubgraphCopy H F) (e : H.edgeSet) :
    c.edgeEquiv e = c.edgeToImage e :=
  rfl

theorem map_isLink_imageGraph (c : SubgraphCopy H F)
    (e : H.edgeSet) (x y : H.vertexSet) :
    H.IsLink e.1 x.1 y.1 ↔
      c.imageGraph.IsLink (c.edgeToImage e).1
        (c.vertexToImage x).1 (c.vertexToImage y).1 := by
  rw [isLink_imageGraph]
  constructor
  · intro h
    have hF := (c.map_isLink e x y).mp h
    exact ⟨⟨⟨e, rfl⟩, hF⟩, ⟨x, rfl⟩, ⟨y, rfl⟩⟩
  · rintro ⟨⟨_, hF⟩, _, _⟩
    exact (c.map_isLink e x y).mpr hF

/-- A represented copy is isomorphic to its image subgraph. -/
noncomputable def graphIso (c : SubgraphCopy H F) :
    GraphIso H c.imageGraph where
  vertexEquiv := c.vertexEquiv
  edgeEquiv := c.edgeEquiv
  map_isLink e x y := by
    simpa only [vertexEquiv_apply, edgeEquiv_apply] using
      c.map_isLink_imageGraph e x y

/-- The reusable final-copy certificate: any exactly represented copy is a
split-off minor of the ambient graph. -/
theorem isSplitOffMinor (c : SubgraphCopy H F) :
    IsSplitOffMinor H F :=
  .trans (.iso c.graphIso) (.subgraph c.imageGraph_le)

end SubgraphCopy

end StrongRoberson
