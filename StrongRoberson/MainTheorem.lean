import StrongRoberson.Oddomorphism
import StrongRoberson.SplitOff

/-!
# Oddomorphisms imply split-off minors

This file records the exact formal target corresponding to Theorem 6 of the
paper (`paper-source/main.tex`, lines 78--81):

> If a graph `F` has an oddomorphism to a graph `G`, then `G` is a split-off
> minor of `F`.

The proof will be developed in subsequent modules. Defining the target as a
proposition keeps this foundational milestone free of `sorry` and other
temporary axioms.
-/

namespace StrongRoberson

universe u

/-- The formal statement that every oddomorphism between finite simple graphs
exhibits its target as a split-off minor of its source.

Both simple graphs are converted to multigraphs before applying
`IsSplitOffMinor`, ensuring that all intermediate operations retain parallel
edges and loops as required by the paper.
-/
def OddomorphismImpliesSplitOffMinor : Prop :=
  ∀ (α γ : Type u) [Finite α] [Finite γ]
    (F : SimpleGraph α) (G : SimpleGraph γ),
    Oddomorphism (simpleToMultiGraph F) G →
      IsSplitOffMinor (simpleToMultiGraph G) (simpleToMultiGraph F)

end StrongRoberson
