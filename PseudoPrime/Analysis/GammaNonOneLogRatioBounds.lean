/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds

/-! # Non-one Gamma witnesses with explicit logarithmic and prefix budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L > 0 with log L ≤ L/2800, the four-fifths cutoff logarithm is at most L/1400.
Compare the cutoff with L² and use log(L²)=2 log L. This isolates the logarithmic
hypothesis from the numerical starting point for subsequent error estimates. -/
theorem nonOne_cutoff_log_of_log_ratio {L : ℝ} (hL0 : 0 < L) (hlogL : Real.log L ≤ L / 2800) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1400 := by
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith only [hc, hlogL]

end PseudoPrime.Analysis
