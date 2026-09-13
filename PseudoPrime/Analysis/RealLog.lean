/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary real-logarithm inequalities

This module contains real-analysis lemmas used by several analytic-number-theory downstream
theorems. Its statements concern positive real numbers and require no number-theoretic
assumptions.
-/

namespace PseudoPrime.Analysis

/-- For positive `y`, the logarithm of `y²` is twice the logarithm of `y`. -/
theorem log_sq_eq_two_mul_log {y : ℝ} (_hy : 0 < y) : Real.log (y ^ 2) = 2 * Real.log y := by
  rw [Real.log_pow]
  norm_num only

/-- The standard tangent-line upper bound for the logarithm, based at a positive `a`. -/
theorem log_le_log_add_sub_div {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    Real.log y ≤ Real.log a + (y - a) / a := by
  have hratio : 0 < y / a := div_pos hy ha
  have hlogRatio := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hy.ne' ha.ne'] at hlogRatio
  calc
    Real.log y = Real.log a + Real.log y - Real.log a := by ring
    _ = Real.log a + (Real.log y - Real.log a) := by rw [add_sub_assoc]
    _ ≤ Real.log a + (y / a - 1) := by
      simpa only [add_comm] using add_le_add_left hlogRatio (Real.log a)
    _ = Real.log a + (y - a) / a := by
      rw [div_eq_mul_inv, div_eq_mul_inv, sub_mul, mul_inv_cancel₀ ha.ne']

end PseudoPrime.Analysis
