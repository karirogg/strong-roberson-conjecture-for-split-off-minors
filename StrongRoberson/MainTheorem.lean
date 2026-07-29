import StrongRoberson.Proof.PaperProof

/-!
# Oddomorphisms imply split-off minors

This file records the exact formal target corresponding to Theorem 6 of the
paper (`paper-source/main.tex`, lines 78--81):

> If a graph `F` has an oddomorphism to a graph `G`, then `G` is a split-off
> minor of `F`.

The proof is developed from the definitions in the imported modules.
-/

namespace StrongRoberson

universe u

/-- Every oddomorphism between finite simple graphs exhibits its target as a
split-off minor of its source (Theorem 6 of the paper).

Both simple graphs are converted to multigraphs so that all intermediate
operations retain parallel edges and loops.
-/
theorem oddomorphism_implies_splitOffMinor
    {α γ : Type u} [Finite α] [Finite γ]
    (F : SimpleGraph α) (G : SimpleGraph γ)
    (φ : Oddomorphism (simpleToMultiGraph F) G) :
    IsSplitOffMinor (simpleToMultiGraph G) (simpleToMultiGraph F) := by
  exact oddomorphism_implies_splitOffMinor_paper F G φ

end StrongRoberson
