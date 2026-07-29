import Mathlib

/-!
# Finite parity bookkeeping

Small `ZMod 2` lemmas used by the parity-preserving reduction for Theorem 6.
They are graph-independent so the operation proofs can reuse them without
repeating set-cardinality calculations.
-/

open Set

namespace StrongRoberson

/-- A natural number is odd exactly when its image in `ZMod 2` is one. -/
theorem odd_iff_cast_zmod_two_eq_one (n : ℕ) :
    Odd n ↔ (n : ZMod 2) = 1 :=
  ZMod.natCast_eq_one_iff_odd.symm

/-- A natural number is even exactly when its image in `ZMod 2` is zero. -/
theorem even_iff_cast_zmod_two_eq_zero (n : ℕ) :
    Even n ↔ (n : ZMod 2) = 0 :=
  ZMod.natCast_eq_zero_iff_even.symm

/-- Every element of `ZMod 2` is represented by zero or one. -/
theorem zmod_two_eq_zero_or_one (x : ZMod 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Removing two distinct elements which are either both present or both
absent does not change a finite set's cardinality modulo two. -/
theorem cast_ncard_sdiff_pair_eq
    {α : Type*} [Finite α] {s : Set α} {a b : α}
    (hab : a ≠ b) (hmem : a ∈ s ↔ b ∈ s) :
    ((s \ {a, b}).ncard : ZMod 2) = (s.ncard : ZMod 2) := by
  classical
  by_cases ha : a ∈ s
  · have hb : b ∈ s := hmem.mp ha
    have hbe : b ∈ s \ {a} := by simp [hb, hab.symm]
    have hs : s \ {a, b} = (s \ {a}) \ {b} := by
      ext x
      simp [and_assoc]
    rw [hs, Set.ncard_sdiff_singleton_of_mem hbe,
      Set.ncard_sdiff_singleton_of_mem ha]
    have hcard : 2 ≤ s.ncard := by
      have : 1 < s.ncard :=
        (Set.one_lt_ncard_iff (s := s)).mpr ⟨a, b, ha, hb, hab⟩
      omega
    have houter : 1 ≤ s.ncard - 1 := by omega
    have hinner : 1 ≤ s.ncard := by omega
    rw [Nat.cast_sub houter, Nat.cast_sub hinner]
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      (s.ncard : ZMod 2) - 1 - 1 =
          (s.ncard : ZMod 2) - 2 := by ring
      _ = (s.ncard : ZMod 2) - 0 := by rw [htwo]
      _ = (s.ncard : ZMod 2) := sub_zero _
  · have hb : b ∉ s := fun hb ↦ ha (hmem.mpr hb)
    have hs : s \ {a, b} = s := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      aesop
    rw [hs]

/-- Cardinality of a disjoint union, cast to `ZMod 2`. -/
theorem cast_ncard_union_eq_add
    {α : Type*} [Finite α] {s t : Set α} (h : Disjoint s t) :
    ((s ∪ t).ncard : ZMod 2) =
      (s.ncard : ZMod 2) + (t.ncard : ZMod 2) := by
  rw [Set.ncard_union_eq h, Nat.cast_add]

/-- Removing one specified point from each side of a disjoint union leaves
the same modulo-two cardinality as the original union. -/
theorem cast_ncard_union_sdiff_pair_eq_add
    {α : Type*} [Finite α] {s t : Set α} {a b : α}
    (hst : Disjoint s t) (ha : a ∈ s) (hb : b ∈ t) :
    (((s ∪ t) \ {a, b}).ncard : ZMod 2) =
      (s.ncard : ZMod 2) + (t.ncard : ZMod 2) := by
  have hab : a ≠ b := by
    intro hab
    subst b
    exact Set.disjoint_left.1 hst ha hb
  calc
    (((s ∪ t) \ {a, b}).ncard : ZMod 2) =
        ((s ∪ t).ncard : ZMod 2) := by
      apply cast_ncard_sdiff_pair_eq hab
      simp [ha, hb]
    _ = (s.ncard : ZMod 2) + (t.ncard : ZMod 2) :=
      cast_ncard_union_eq_add hst

end StrongRoberson
