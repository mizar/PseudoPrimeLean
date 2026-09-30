/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Logarithmic ratios and a logarithmic correction

This module defines two real logarithmic ratios, computes their derivatives at positive inputs,
and proves that both are strictly decreasing on `[8, ∞)`. It also defines the elementary
correction `log 2 * (2 log y - log 2)`. No character or L-function hypotheses are used.
-/

namespace PseudoPrime.Analysis

/-- The logarithmic ratio `(2 log y + 1)/y`, used in real-variable comparisons. -/
noncomputable def logLinearRatio (y : ℝ) : ℝ :=
  (2 * Real.log y + 1) / y

/-- The squared-log ratio `(log y)²/y`, used in real-variable comparisons. -/
noncomputable def logSquareRatio (y : ℝ) : ℝ :=
  (Real.log y) ^ 2 / y

/-- The derivative of the logarithmic ratio at a positive input. -/
theorem hasDerivAt_logLinearRatio {y : ℝ} (hy : 0 < y) :
    HasDerivAt logLinearRatio ((1 - 2 * Real.log y) / y ^ 2) y := by
  unfold logLinearRatio
  have hraw := (((Real.hasDerivAt_log hy.ne').const_mul 2).add_const 1).div (hasDerivAt_id y) hy.ne'
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · simp only [id_eq]
    congr 1
    have hinv : y⁻¹ * y = 1 := inv_mul_cancel₀ hy.ne'
    rw [mul_assoc, hinv]
    ring
  · filter_upwards with z
    simp only [Pi.div_apply, id_eq]

/-- The logarithmic ratio is strictly decreasing on `[8, ∞)`. -/
theorem strictAntiOn_logLinearRatio : StrictAntiOn logLinearRatio (Set.Ici 8) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 8)
  · intro y hy
    simp only [Set.mem_Ici] at hy
    have hderiv := hasDerivAt_logLinearRatio (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hy)
    exact hderiv.continuousAt.continuousWithinAt
  · intro y hy
    simp only [interior_Ici, Set.mem_Ioi] at hy
    rw [(hasDerivAt_logLinearRatio (lt_trans (by norm_num only : (0 : ℝ) < 8) hy)).deriv]
    have hlog : (1 / 2 : ℝ) < Real.log y := by
      have hlogTwoY : Real.log 2 < Real.log y :=
        Real.strictMonoOn_log (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi])
          (show y ∈ Set.Ioi 0 by exact lt_trans (by norm_num only : (0 : ℝ) < 8) hy)
          (lt_trans (by norm_num only : (2 : ℝ) < 8) hy)
      exact (show (1 / 2 : ℝ) < Real.log 2 by linarith only [Real.log_two_gt_d9]).trans hlogTwoY
    exact
      div_neg_of_neg_of_pos (by linarith only [hlog])
        (sq_pos_of_pos (lt_trans (by norm_num only : (0 : ℝ) < 8) hy))

/-- The derivative of the squared-log ratio at a positive input. -/
theorem hasDerivAt_logSquareRatio {y : ℝ} (hy : 0 < y) :
    HasDerivAt logSquareRatio (Real.log y * (2 - Real.log y) / y ^ 2) y := by
  unfold logSquareRatio
  have hraw := ((Real.hasDerivAt_log hy.ne').pow 2).div (hasDerivAt_id y) hy.ne'
  apply (hraw.congr_of_eventuallyEq ?_).congr_deriv
  · simp only [Pi.pow_apply, id_eq]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hy.ne']
    ring
  · filter_upwards with z
    simp only [Pi.div_apply, Pi.pow_apply, id_eq]

/-- The squared-log ratio is strictly decreasing on `[8, ∞)`. -/
theorem strictAntiOn_logSquareRatio : StrictAntiOn logSquareRatio (Set.Ici 8) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 8)
  · intro y hy
    simp only [Set.mem_Ici] at hy
    have hderiv := hasDerivAt_logSquareRatio (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hy)
    exact hderiv.continuousAt.continuousWithinAt
  · intro y hy
    simp only [interior_Ici, Set.mem_Ioi] at hy
    rw [(hasDerivAt_logSquareRatio (lt_trans (by norm_num only : (0 : ℝ) < 8) hy)).deriv]
    have hlogPos : 0 < Real.log y := Real.log_pos (lt_trans (by norm_num only : (1 : ℝ) < 8) hy)
    have hlogEightY : Real.log 8 < Real.log y :=
      Real.strictMonoOn_log (show (8 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi])
        (show y ∈ Set.Ioi 0 by exact lt_trans (by norm_num only : (0 : ℝ) < 8) hy) hy
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow] at hlogEightY
    norm_num only [Nat.cast_ofNat] at hlogEightY
    have htwoLog : (2 : ℝ) < Real.log y := by linarith only [hlogEightY, Real.log_two_gt_d9]
    exact
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hlogPos (sub_neg.mpr htwoLog))
        (sq_pos_of_pos (lt_trans (by norm_num only : (0 : ℝ) < 8) hy))

/-- The real function `log 2 * (2 log y - log 2)`, equal to `log 2 * log (y²/2)` for `y > 0`. -/
noncomputable def logTwoSquareCorrection (y : ℝ) : ℝ :=
  Real.log 2 * (2 * Real.log y - Real.log 2)

end PseudoPrime.Analysis
