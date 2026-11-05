/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalRatioCell

/-! # Contiguous even-anchor ratio coverage -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check that valid even-anchor ratio cells overlap and cover the interval from `lo`
through `hi`. The recursion ends when a checked cell reaches the target endpoint. -/
def localRatioCoverCheck (lo hi : ℚ) : List LocalRatioCell → Bool
  | [] => false
  | c :: cs =>
    (c.check && decide (c.lo ≤ lo ∧ lo ≤ c.hi)) &&
      (decide (hi ≤ c.hi) || localRatioCoverCheck c.hi hi cs)

/-- A successful contiguous even-anchor check bounds the local envelope by the squared
`96467/100000` multiple on the entire interval. Induction selects a cell containing the
actual scale and applies its anchor comparison. -/
theorem localRatioCoverCheck_sound (cells : List LocalRatioCell) (lo hi : ℚ)
    (hcheck : localRatioCoverCheck lo hi cells = true) {s : ℝ} (hlo : (lo : ℝ) ≤ s)
    (hhi : s ≤ (hi : ℝ)) : localFullEnvelope s ≤ ((96467 / 100000 : ℝ) * s) ^ 2 := by
  induction cells generalizing lo with
  | nil => simp only [localRatioCoverCheck, Bool.false_eq_true] at hcheck
  | cons c cs
    ih =>
    have hc :
      ((c.check && decide (c.lo ≤ lo ∧ lo ≤ c.hi)) &&
          (decide (hi ≤ c.hi) || localRatioCoverCheck c.hi hi cs)) =
        true := by
      simpa only [localRatioCoverCheck] using hcheck
    have hparts := Bool.and_eq_true_iff.mp hc
    have hleft := Bool.and_eq_true_iff.mp hparts.1
    have hadj : c.lo ≤ lo ∧ lo ≤ c.hi := of_decide_eq_true hleft.2
    by_cases hcell : s ≤ (c.hi : ℝ)
    · exact c.sound hleft.1 (((Rat.cast_le (K := ℝ)).mpr hadj.1).trans hlo) hcell
    · have hnot : ¬hi ≤ c.hi := by
        intro h
        exact hcell (hhi.trans ((Rat.cast_le (K := ℝ)).mpr h))
      have hrest : localRatioCoverCheck c.hi hi cs = true := by
        rcases Bool.or_eq_true_iff.mp hparts.2 with hend | hnext
        · exact (hnot (of_decide_eq_true hend)).elim
        · exact hnext
      exact ih c.hi hrest (le_of_lt (lt_of_not_ge hcell))

end PseudoPrime.PrimeTestBounds.MillerRabin
