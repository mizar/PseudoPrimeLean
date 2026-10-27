/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicEulerCertificate
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.RealLog

/-! # Continuous dyadic ramp bounds at small scales -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For `x ≥ 1600`, a tangent estimate at `sqrt x = 40` bounds the logarithmic
ramp envelope by `9/40`. This supplies the continuous dyadic local estimate. -/
theorem dyadic_ramp_log_bound_of_ge_1600 {x : ℝ} (hx : 1600 ≤ x) :
    (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ (9 / 40 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have ht : (40 : ℝ) ≤ Real.sqrt x :=
    (Real.le_sqrt (by norm_num only) hx0.le).mpr
      (by
        norm_num only; exact hx)
  have ht0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have htan := log_le_log_add_sub_div (a := (40 : ℝ)) (y := Real.sqrt x) (by norm_num only) ht0
  have he : Real.log (7920 : ℝ) = Real.log (99 / 40 : ℝ) + 2 * Real.log 40 + Real.log 2 := by
    rw [show (7920 : ℝ) = (99 / 40) * 40 ^ 2 * 2 by norm_num only,
      Real.log_mul (by norm_num only : ((99 / 40 : ℝ) * 40 ^ 2) ≠ 0)
        (by norm_num only : (2 : ℝ) ≠ 0),
      Real.log_mul (by norm_num only : (99 / 40 : ℝ) ≠ 0) (by norm_num only : (40 : ℝ) ^ 2 ≠ 0),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hc : rationalLogIntervalCheck 7920 13 10 (89 / 10) 9 = true := by decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat] at hl
  have hs := Real.log_sqrt hx0.le
  rw [Real.log_mul (by norm_num only : (99 / 40 : ℝ) ≠ 0) hx0.ne']
  apply (div_le_iff₀ ht0).mpr
  linarith only [htan, he, hl, hs, ht]

/-- For `x ≥ 1600`, the logarithmic upper bound for the dyadic power count,
including one endpoint, has normalized cost at most `9/40`. -/
theorem dyadic_count_weighted_bound_of_ge_1600 {x : ℝ} (hx : 1600 ≤ x) :
    Real.log 2 * ((gammaRampPowerCount 2 x + 1) / Real.sqrt x) ≤ (9 / 40 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hr :=
    div_le_div_of_nonneg_right
      (add_le_add
        (gamma_ramp_count_le_log (by norm_num only : 1 < (2 : ℕ))
          (by linarith only [hx] : (1 : ℝ) ≤ x))
        (le_refl (1 : ℝ)))
      (Real.sqrt_nonneg x)
  have hw := mul_le_mul_of_nonneg_left hr hl0.le
  have he :
    Real.log 2 * ((Real.log ((99 / 40 : ℝ) * x) / Real.log 2 + 1) / Real.sqrt x) =
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x := by
    rw [← mul_div_assoc, mul_add, mul_one,
      mul_comm (Real.log 2) (Real.log ((99 / 40 : ℝ) * x) / Real.log 2), div_mul_cancel₀ _ hl0.ne']
  norm_num only [Nat.cast_ofNat] at hw
  rw [he] at hw
  exact hw.trans (dyadic_ramp_log_bound_of_ge_1600 hx)

/-- For `x ≥ 1600`, the dyadic ramp correction for character value zero has
normalized logarithmic cost at most `9/40`, by the power-count envelope. -/
theorem dyadic_zero_ramp_le_of_ge_1600 {x : ℝ} (hx : 1600 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection 0 ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (9 / 40 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hr := gamma_ramp_zero_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0
  have hc :=
    div_le_div_of_nonneg_right
      (show gammaRampPowerCount 2 x ≤ gammaRampPowerCount 2 x + 1 by linarith only)
      (Real.sqrt_nonneg x)
  norm_num only [Nat.cast_ofNat] at hr
  exact
    (mul_le_mul_of_nonneg_left (hr.trans hc)
          (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2))).trans
      (dyadic_count_weighted_bound_of_ge_1600 hx)

/-- For `x ≥ 1600`, the dyadic ramp correction for character value minus one has
normalized logarithmic cost at most `9/40`, retaining the parity count. -/
theorem dyadic_minus_one_ramp_le_of_ge_1600 {x : ℝ} (hx : 1600 ≤ x) :
    Real.log 2 *
        ((∑' k : ℕ, exponentialRampLocalCorrection (-1) ((2 : ℝ) ^ (k + 1) / x) (k + 1)) /
          Real.sqrt x) ≤
      (9 / 40 : ℝ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hr := gamma_ramp_neg_one_series_le_count (by norm_num only : 1 < (2 : ℕ)) hx0
  norm_num only [Nat.cast_ofNat] at hr
  exact
    (mul_le_mul_of_nonneg_left hr (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2))).trans
      (dyadic_count_weighted_bound_of_ge_1600 hx)

end PseudoPrime.Analysis
