/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaCriticalLine
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # A rational height-weighted Gamma majorant -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For any real input, retain the first four nonnegative terms of the cosh
series. The resulting sextic polynomial is a global lower bound, without a grid. -/
theorem cosh_ge_sextic (z : ℝ) : 1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 ≤ Real.cosh z := by
  have hn (n : ℕ) : 0 ≤ z ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg z) n
  have h := Summable.sum_le_tsum (Finset.range 4) (fun n _ ↦ hn n) (Real.hasSum_cosh z).summable
  rw [(Real.hasSum_cosh z).tsum_eq] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial] at h
  nlinarith only [h]

/-- For every real height, t^2*(1+t^2)^2 is at most cosh(pi*t).
Use the sextic series bound, pi>3 and nonnegative even powers. This supplies a
rational height envelope for Gamma on the critical half line. -/
theorem cosh_pi_mul_ge_height_polynomial (t : ℝ) :
    t ^ 2 * (1 + t ^ 2) ^ 2 ≤ Real.cosh (Real.pi * t) := by
  have h := cosh_ge_sextic (Real.pi * t)
  rw [mul_pow, mul_pow, mul_pow] at h
  have h2 :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 2) (sq_nonneg t)
  have h4 :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 4)
      (pow_nonneg (sq_nonneg t) 2)
  have h6 :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 3) Real.pi_gt_three.le 6)
      (pow_nonneg (sq_nonneg t) 3)
  norm_num only [pow_mul] at h4 h6
  nlinarith only [h, h2, h4, h6, sq_nonneg t, pow_nonneg (sq_nonneg t) 2,
    pow_nonneg (sq_nonneg t) 3]

/-- At every real height, |t|*norm(Gamma(1/2+i*t))<=2/(1+t^2).
Combine the exact Gamma norm identity with the sextic cosh bound and pi<4.
This integrable resolvent majorizes the derivative of the logarithmic scale phase. -/
theorem gammaHalf_height_le_two_resolvent (t : ℝ) :
    |t| * ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ 2 / (1 + t ^ 2) := by
  have hp := cosh_pi_mul_ge_height_polynomial t
  have hw :=
    mul_le_mul_of_nonneg_right Real.pi_lt_four.le (mul_nonneg (sq_nonneg t) (sq_nonneg (1 + t ^ 2)))
  have hnum : Real.pi * t ^ 2 * (1 + t ^ 2) ^ 2 ≤ 4 * Real.cosh (Real.pi * t) := by
    nlinarith only [hw, hp]
  have hs : (|t| * ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ * (1 + t ^ 2)) ^ 2 ≤ 4 := by
    rw [mul_pow, mul_pow, sq_abs, norm_Gamma_half_add_I_sq]
    convert (div_le_iff₀ (Real.cosh_pos (Real.pi * t))).mpr hnum using 1
    ring
  apply (le_div_iff₀ (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2)).mpr
  nlinarith only [hs]

end PseudoPrime.Analysis
