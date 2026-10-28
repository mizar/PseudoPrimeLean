/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeNonOneBounds
public import PseudoPrime.LLS.GammaPrincipalEulerCharacterBounds
public import PseudoPrime.LLS.GammaRetainedCommonCostBounds

/-! # Non-one witnesses from retained real-axis Euler budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L > 0 and log L ≤ L/2000, the four-fifths cutoff logarithm is at most L/1000.
Compare the cutoff with L² and double the logarithm bound. This weaker logarithmic
hypothesis permits smaller starting scales in the retained Euler comparison. -/
theorem nonOne_cutoff_log_of_wide_ratio {L : ℝ} (hL0 : 0 < L) (hlogL : Real.log L ≤ L / 2000) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1000 := by
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith only [hc, hlogL]

end PseudoPrime.Analysis
