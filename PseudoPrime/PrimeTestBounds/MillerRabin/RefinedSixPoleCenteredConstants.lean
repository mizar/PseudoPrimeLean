/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredScale
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperConstants

/-! # Unit-weight constants for centered principal estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Twelve positive Taylor terms give a sufficiently sharp rational upper bound
for the unit-cutoff exponential factor. -/
theorem refined_exp_neg_unit_sharp : Real.exp (-(567 / 200 : ℝ)) ≤ 58721 / 1000000 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 567 / 200) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    pow_zero, pow_one] at h
  have hb : (1000000 / 58721 : ℝ) ≤ Real.exp (567 / 200 : ℝ) := by linarith only [h]
  rw [Real.exp_neg, ← one_div]
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 1000000 / 58721) hb
  norm_num only at hi ⊢
  exact hi

/-- The normalized unit-cutoff weight is at most `61/1000`; this coefficient
is used for the square-root and inverse-square-root Chebyshev costs. -/
theorem refined_unit_weight_centered : refinedWeight 1 ≤ (61 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have he := refined_exp_neg_unit_sharp
  norm_num only [refinedWeight, refinedCoord, Real.log_one, Real.sqrt_one, mul_zero, sub_zero,
    mul_one]
  nlinarith only [he]

/-- The normalized absolute unit-cutoff derivative is at most `81/1000`.
The existing derivative estimate suffices after a rational comparison. -/
theorem refined_unit_deriv_centered :
    |refinedWeightDeriv 1| ≤ (81 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h := refined_deriv_unit_lt
  norm_num only at ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
