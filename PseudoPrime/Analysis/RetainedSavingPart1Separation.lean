/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPart1Separation

/-! # Part 1 separation retaining the positive auxiliary saving -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For y ≥ L > 8 and nonnegative A,w, the actual Part 1 bounds are
incompatible when y-L ≥ 2 log L+7031/5000+w-2A and the displayed fixed
constants hold. Retain the positive A(1+log y) contribution, apply the
logarithm tangent and only then use the correction inequality again.
This is the reusable scalar separation for the smaller Part 1 radius. -/
theorem refinedPart1_bounds_incompatible_retained_saving {L y A w b P T U : ℝ} (hL : 8 < L)
    (hy : L ≤ y) (hA : 0 ≤ A) (hw : 0 ≤ w) (hb : b ≤ (231 / 10000 : ℝ)) (hP : (57 / 50 : ℝ) ≤ P)
    (hT : T ≤ (1839 / 1000 : ℝ)) (hB : 2 * Real.log L + 7031 / 5000 + w - 2 * A ≤ y - L)
    (hupper :
      U ≤
        (2 * y + 2 + Real.log (y ^ 2)) * (L / 2 + 9 / 50 - A) +
            (1 / 2 : ℝ) * (L - P) * Real.log (y ^ 2) -
          11 / 4)
    (hlower : y ^ 2 - y * (2 * b + w) - T * Real.log (y ^ 2) - 1 - 2 * b ≤ U) : False := by
  have hL0 : 0 < L := by linarith only [hL]
  have hy0 : 0 < y := hL0.trans_le hy
  have hu := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hL.le
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  have hu2 : 2 < Real.log L := by linarith only [hu, Real.log_two_gt_d9]
  have hlogmono := Real.log_le_log hL0 hy
  have hlog := log_le_log_add_sub_div (a := L) (y := y) hL0 hy0
  have htangent := mul_le_mul_of_nonneg_right hlog hL0.le
  rw [add_mul, div_mul_cancel₀ _ hL0.ne'] at htangent
  have hratio := mul_nonneg (sub_nonneg.mpr hL.le) (sub_nonneg.mpr hlogmono)
  have hbu := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hu2.le)
  have ha := mul_nonneg hA (show 0 ≤ Real.log y - 2 by linarith only [hlogmono, hu2])
  have hby := mul_le_mul_of_nonneg_right hB hy0.le
  have hp := mul_le_mul_of_nonneg_right hP (show 0 ≤ Real.log y by linarith only [hlogmono, hu2])
  have ht := mul_le_mul_of_nonneg_right hT (show 0 ≤ Real.log y by linarith only [hlogmono, hu2])
  have hz := mul_le_mul_of_nonneg_right hb (show 0 ≤ 2 * y + 2 by linarith only [hy0])
  rw [Real.log_pow] at hupper hlower
  norm_num only [Nat.cast_ofNat] at hupper hlower
  have hmain :
    y * (2 * Real.log L + 1) - L * (1 + 2 * Real.log y) - (1449 / 500 : ℝ) * Real.log y +
        2 * A * (1 + Real.log y) +
        6719 / 5000 ≤
      0 := by
    nlinarith only [hupper, hlower, hby, hp, ht, hz]
  nlinarith only [hmain, htangent, hratio, hbu, ha, hB, hw, hu2, hy0]

end PseudoPrime.Analysis
