/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TheoreticalKernelNumerics

/-! # Refined gamma certificates for indices four through six

Finite positive Taylor sums give exponential upper bounds and strict
coefficient certificates with the inflated mass cap 4710471/10000000.
The conductor-sensitive least-prime comparison consumes these certificates.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At scale 11/6, ten Taylor terms certify the small-denominator exponential
upper bound used by the index-four gamma certificate. -/
theorem gamma_four_small_denominator_exp_bound : Real.exp (-(11 / 6 : ℝ)) ≤ 55 / 344 := by
  apply exp_neg_le_of_taylor (by norm_num only) (by norm_num only) 10
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- At scale 11/6, the rational exponential bound gives denominator at least
203/86. Squaring this bound preserves coefficient 6571/10000 with the inflated
mass majorant; it supplies the conductor-sum prime bound. -/
theorem gamma_four_small_denominator_coefficient :
    (11 / 6 : ℝ) * (3 * (4710471 / 10000000)) ^ 2 <
      (6571 / 10000) * (3 - 4 * Real.exp (-(11 / 6 : ℝ))) ^ 2 := by
  have he := gamma_four_small_denominator_exp_bound
  have hd : (203 / 86 : ℝ) ≤ 3 - 4 * Real.exp (-(11 / 6 : ℝ)) := by linarith only [he]
  have hs := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 203 / 86) hd
  nlinarith only [hs]

/-- The displayed positive Taylor sum bounds the negative exponential at index 5. -/
theorem refined_gamma_five_exp_bound : Real.exp (-(171 / 100 : ℝ)) ≤ 90433 / 500000 := by
  apply exp_neg_le_of_taylor (by norm_num only) (by norm_num only) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- The exponential upper bound gives a positive denominator lower bound.
Squaring that bound verifies the strict kernel certificate with the inflated
mass majorant 4710471/10000000 for the small-index conductor comparison. -/
theorem refined_gamma_five_coefficient :
    (171 / 100 : ℝ) * (4 * (4710471 / 10000000)) ^ 2 <
      (6336 / 10000) * (4 - 5 * Real.exp (-(171 / 100 : ℝ))) ^ 2 := by
  have he := refined_gamma_five_exp_bound
  have hd : (309567 / 100000 : ℝ) ≤ 4 - 5 * Real.exp (-(171 / 100 : ℝ)) := by linarith only [he]
  have hs := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 309567 / 100000) hd
  nlinarith only [hs]

/-- The displayed positive Taylor sum bounds the negative exponential at index 6. -/
theorem refined_gamma_six_exp_bound : Real.exp (-(1633 / 1000 : ℝ)) ≤ 195343 / 1000000 := by
  apply exp_neg_le_of_taylor (by norm_num only) (by norm_num only) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]

/-- The exponential upper bound gives a positive denominator lower bound.
Squaring that bound verifies the strict kernel certificate with the inflated
mass majorant 4710471/10000000 for the small-index conductor comparison. -/
theorem refined_gamma_six_coefficient :
    (1633 / 1000 : ℝ) * (5 * (4710471 / 10000000)) ^ 2 <
      (6183 / 10000) * (5 - 6 * Real.exp (-(1633 / 1000 : ℝ))) ^ 2 := by
  have he := refined_gamma_six_exp_bound
  have hd : (1913971 / 500000 : ℝ) ≤ 5 - 6 * Real.exp (-(1633 / 1000 : ℝ)) := by linarith only [he]
  have hs := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 1913971 / 500000) hd
  nlinarith only [hs]

end PseudoPrime.LLS.PaperStatements
