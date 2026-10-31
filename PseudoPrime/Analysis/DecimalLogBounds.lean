/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics

/-! # Logarithmic lower bounds for arbitrary decimal exponents -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A decimal cutoff 10^d≤n gives log n≥(23/10)d.
Use logarithmic monotonicity and the proved lower bound for log 10.
Keep d variable to avoid evaluating enormous natural powers. -/
theorem gaussianMR_log_of_decimal {n d : ℕ} (hn : 10 ^ d ≤ n) : (23 / 10 : ℝ) * d ≤ Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) d)
      (by exact_mod_cast hn : (10 : ℝ) ^ d ≤ n)
  rw [Real.log_pow] at h
  exact
    (mul_le_mul_of_nonneg_right log_ten_gt_twenty_three_tenths.le (Nat.cast_nonneg d)).trans
      (by simpa only [mul_comm] using h)

end PseudoPrime.Analysis
