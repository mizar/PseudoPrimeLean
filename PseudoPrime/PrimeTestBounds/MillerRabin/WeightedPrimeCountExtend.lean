/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCount

/-! # Extending weighted prime-product counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The weighted product count is monotone in its budget. Strong induction
on the larger budget and the recurrence cover every weight, including zero. -/
theorem weightedPrimeCount_mono (w : ℕ → ℕ) (xs : List ℕ) {a b : ℕ} (hab : a ≤ b) :
    weightedPrimeCount w xs a ≤ weightedPrimeCount w xs b := by
  induction b using Nat.strong_induction_on generalizing xs a with
  | h b ih =>
    induction xs with
    | nil => rw [weightedPrimeCount.eq_def, weightedPrimeCount.eq_def]
    | cons p ps ip =>
      rw [weightedPrimeCount.eq_def, weightedPrimeCount.eq_def]
      by_cases hp : 0 < w p
      · simp only [hp, dite_true]
        by_cases ha : w p ≤ a
        · have hb : w p ≤ b := ha.trans hab
          simp only [ha, hb, dite_true]
          exact
            Nat.add_le_add ip
              (ih (b - w p) (Nat.sub_lt (lt_of_lt_of_le hp hb) hp) (p :: ps)
                (Nat.sub_le_sub_right hab _))
        · simp only [ha, dite_false]
          by_cases hb : w p ≤ b
          · simp only [hb, dite_true]
            exact ip.trans (Nat.le_add_right _ _)
          · simp only [hb, dite_false]
            exact ip
      · simp only [hp, dite_false, le_refl]

/-- A budget enlarged by `k` copies of a positive weight counts at least
`k + 1` copies of the old tail count. The recurrence separates the number
of occurrences of the first label. -/
theorem weightedPrimeCount_repeat_lower (p A k : ℕ) (ps : List ℕ) (hp : 0 < p) :
    (k + 1) * weightedPrimeCount id ps A ≤ weightedPrimeCount id (p :: ps) (A + k * p) := by
  induction k with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.one_mul]
    conv_rhs => rw [weightedPrimeCount.eq_def]
    dsimp only [id_eq]
    rw [dite_eq_left hp]
    by_cases hf : p ≤ A
    · simp only [hf, dite_true]
      exact Nat.le_add_right _ _
    · simp only [hf, dite_false, le_refl]
  | succ k ih =>
    have hf : p ≤ A + (k + 1) * p := by nlinarith only [hp]
    have heq : A + (k + 1) * p - p = A + k * p := by
      rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_sub_cancel]
    conv_rhs => rw [weightedPrimeCount.eq_def]
    dsimp only [id_eq]
    rw [dite_eq_left hp, dite_eq_left hf, heq]
    have hmono := weightedPrimeCount_mono id ps (show A ≤ A + (k + 1) * p from Nat.le_add_right _ _)
    nlinarith only [hmono, ih]

end PseudoPrime.PrimeTestBounds.MillerRabin
