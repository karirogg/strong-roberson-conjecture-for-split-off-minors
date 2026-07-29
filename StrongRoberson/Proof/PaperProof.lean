import StrongRoberson.Proof.Reduction

/-!
# Assembly of the paper proof

This module contains only the final composition:

1. reduce the oddomorphism to the perfect-fibre case;
2. apply the paper's lift lemma; and
3. compose the two split-off-minor certificates.
-/

namespace StrongRoberson

universe u

theorem oddomorphism_implies_splitOffMinor_paper
    {α γ : Type u} [Finite α] [Finite γ]
    (F : SimpleGraph α) (G : SimpleGraph γ)
    (φ : Oddomorphism (simpleToMultiGraph F) G) :
    IsSplitOffMinor (simpleToMultiGraph G) (simpleToMultiGraph F) := by
  let R :=
    oddomorphism_has_perfectFiberReduction
      (simpleToMultiGraph F) G φ
  exact IsSplitOffMinor.trans
    (perfectFibers_implies_splitOffMinor R.graph G R.hom R.perfect)
    R.isSplitOffMinor

end StrongRoberson
