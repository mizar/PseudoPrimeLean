/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Internally certified precise bounds on log two -/

public section

namespace PseudoPrime.Analysis

-- The exact 64-term rational logarithm series requires a deeper reduction stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
-- The kernel checks the rational interval without using a numerical table.
private theorem log_half_check :
    rationalLogIntervalCheck (1 / 2) 0 64 (-693147180559946 / 1000000000000000)
        (-693147180559945 / 1000000000000000) =
      true := by
  decide +kernel

/-- The logarithm of two lies in a rational interval of width `10⁻¹⁵`. A kernel-checked
64-term Taylor interval for `log(1/2)` and the logarithm quotient identity provide both
inequalities, without a precomputed logarithm table. -/
theorem log_two_precise :
    (693147180559945 / 1000000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (693147180559946 / 1000000000000000 : ℝ) := by
  have h := rationalLogIntervalCheck_sound log_half_check
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num only) (by norm_num only), Real.log_one, zero_sub]
  rw [hlog] at h
  constructor <;> linarith only [h.1, h.2]

end PseudoPrime.Analysis
