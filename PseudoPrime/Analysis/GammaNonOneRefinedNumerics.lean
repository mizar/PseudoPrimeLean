/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneNumerics
public import PseudoPrime.LLS.PaperStatements.GammaNonOneRefinedNumerics

/-! # Sharper non-one Gamma error budgets

A variable decay anchor and the exact level-four logarithm cost reduce the threshold.
All estimates hold throughout logarithmic scales at least 39400.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The level-four logarithm cost is at most 7/5. Bound exp(7/5) from below by a
 finite Taylor sum and the certified exp(1) bound. This retains a smaller conductor cost. -/
theorem log_four_le_seven_fifths : Real.log (4 : ℝ) ≤ 7 / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 4)).mpr
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 :=
    (by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2 / 5) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ht
  rw [show (7 / 5 : ℝ) = 1 + 2 / 5 by norm_num only, Real.exp_add]
  have hm := mul_le_mul he ht (by norm_num only) (Real.exp_pos 1).le
  exact (by norm_num only : (4 : ℝ) ≤ (27 / 10) * (559 / 375)).trans hm

end PseudoPrime.Analysis
