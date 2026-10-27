/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

/-! # Scalar absorption for reciprocal zero-mass bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For y≥L>8, A≥0, and P≥57/50, the reciprocal raw inequality implies
b≤L/2+9/50−A. Multiply by y² and compare the resulting polynomials using
(y−1)(y−L), (P/2−57/100)(y²−1), and A(2y−1), all nonnegative.
This removes the reciprocal denominator while retaining the lower-bound saving A. -/
theorem reciprocalZeroMass_le_refined_bound {L y A P b : ℝ} (hL : 8 < L) (hyL : L ≤ y) (hA : 0 ≤ A)
    (hP : (57 / 50 : ℝ) ≤ P)
    (hraw : (1 - 1 / y) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - A - 1 / 4) :
    b ≤ L / 2 + 9 / 50 - A := by
  have hy : 0 < y := lt_of_lt_of_le (lt_trans (by norm_num only : (0 : ℝ) < 8) hL) hyL
  have hm := mul_le_mul_of_nonneg_left hraw (sq_nonneg y)
  have hleft : y ^ 2 * ((1 - 1 / y) ^ 2 * b) = (y - 1) ^ 2 * b := by field_simp [hy.ne']
  have hright :
    y ^ 2 * ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - A - 1 / 4) =
      (1 / 2 : ℝ) * (y ^ 2 - 1) * (L - P) - A * y ^ 2 - (1 / 4 : ℝ) * y ^ 2 := by
    field_simp [hy.ne']
  rw [hleft, hright] at hm
  have h1 : 0 ≤ (y - 1) * (y - L) := mul_nonneg (by linarith only [hL, hyL]) (sub_nonneg.mpr hyL)
  have h2 : 0 ≤ (P / 2 - 57 / 100) * (y ^ 2 - 1) :=
    mul_nonneg (by linarith only [hP]) (by nlinarith only [hL, hyL])
  have h3 : 0 ≤ A * (2 * y - 1) := mul_nonneg hA (by linarith only [hL, hyL])
  have hu :
    (1 / 2 : ℝ) * (y ^ 2 - 1) * (L - P) - A * y ^ 2 - (1 / 4 : ℝ) * y ^ 2 ≤
      (y - 1) ^ 2 * (L / 2 + 9 / 50 - A) := by
    nlinarith only [h1, h2, h3, hL, hyL]
  have hc : 0 < (y - 1) ^ 2 := sq_pos_of_pos (by linarith only [hL, hyL])
  exact (mul_le_mul_iff_right₀ hc).mp (hm.trans hu)

end PseudoPrime.Analysis
