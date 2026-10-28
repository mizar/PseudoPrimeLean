/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneNumerics

/-! # Sharper non-one Gamma error budgets

A variable decay anchor and the exact level-four logarithm cost reduce the threshold.
All estimates hold throughout logarithmic scales at least 39400.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive a and x≥a^16, the left-line decay is at most 1/(a sqrt(x)).
 Separate the exponents and use monotonicity of the negative real power.
 This allows a sharper decay anchor than the fixed integer three. -/
theorem rpow_neg_nine_sixteenths_le_div_scale_sqrt {a x : ℝ} (ha : 0 < a) (hx : a ^ (16 : ℕ) ≤ x) :
    x ^ (-9 / 16 : ℝ) ≤ 1 / (a * Real.sqrt x) := by
  have hxpos := (pow_pos ha 16).trans_le hx
  have hsmall :=
    Real.rpow_le_rpow_of_nonpos (pow_pos ha 16) hx (by norm_num only : (-1 / 16 : ℝ) ≤ 0)
  have hbase : (a ^ (16 : ℕ)) ^ (-1 / 16 : ℝ) = 1 / a := by
    rw [← Real.rpow_natCast_mul ha.le]
    norm_num only [Real.rpow_neg_one, one_div]
  have hhalf : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [neg_div, Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hbase] at hsmall
  calc
    _ = x ^ (-1 / 16 : ℝ) * x ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num only
    _ ≤ (1 / a) * (1 / Real.sqrt x) := by
      rw [hhalf]
      exact mul_le_mul_of_nonneg_right hsmall (div_nonneg zero_le_one (Real.sqrt_nonneg x))
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements
