/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S1
public import PseudoPrime.Analysis.RationalPart1Separation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactorSplitBounds
public import PseudoPrime.LLS.RationalTheorem11S12

/-! # Rational Part 1 radius and universal logarithmic profile -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L > 0, log L/L^(3/8) ≤ 491/500. Apply the logarithm tangent at
1359/500 to L^(3/8) and use the certified exponential lower bound at one.
This supplies the rational factor-support parameter for exponent 5/8. -/
theorem log_div_rpow_three_eighths_le {L : ℝ} (hL : 0 < L) :
    Real.log L / L ^ (3 / 8 : ℝ) ≤ 491 / 500 := by
  have hu0 := Real.rpow_pos_of_pos hL (3 / 8 : ℝ)
  have ht := Real.log_le_sub_one_of_pos (div_pos hu0 (by norm_num only : (0 : ℝ) < 1359 / 500))
  rw [Real.log_div hu0.ne' (by norm_num only : (1359 / 500 : ℝ) ≠ 0), Real.log_rpow hL] at ht
  have ha : Real.log (1359 / 500 : ℝ) < 1 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 1359 / 500)).mpr
    exact (by norm_num only : (1359 / 500 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  rw [div_le_iff₀ hu0]
  linarith only [ht, ha, hu0]

end PseudoPrime.Analysis
