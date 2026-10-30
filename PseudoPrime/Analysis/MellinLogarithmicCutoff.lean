/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogarithmicPowerAbsorption

/-! # Logarithmic cutoff and correction bounds -/

public section

namespace PseudoPrime.Analysis

/-- For y at least two, the logarithm of the eighth-power height cutoff plus two
is at most nine times log y. Compare its argument with y to the ninth power.
This converts the zero-free logarithmic denominator to a fixed log-log power. -/
theorem log_eighth_power_cutoff_le {y : ℝ} (hy : 2 ≤ y) :
    Real.log (y ^ 8 + 2) ≤ 9 * Real.log y := by
  have hy0 : 0 ≤ y := (by norm_num only : (0 : ℝ) ≤ 2).trans hy
  have hy1 : 1 ≤ y := (by norm_num only : (1 : ℝ) ≤ 2).trans hy
  have hp : 2 ≤ y ^ 8 := hy.trans (le_self_pow₀ hy1 (by decide : 8 ≠ 0))
  have hm := mul_nonneg (sub_nonneg.mpr hy) (pow_nonneg hy0 8)
  have hpow : y ^ 8 + 2 ≤ y ^ 9 := by
    rw [pow_succ]
    nlinarith only [hm, hp]
  exact
    (Real.log_le_log (by positivity) hpow).trans_eq
      (by
        rw [Real.log_pow]; norm_num only)

/-- For positive x with log x at least two, a positive gap saving at least
324*log(log x)^3 relative to log x bounds the low-zero cutoff power by x/log(x)^4.
Compare logarithmic exponents using the eighth-power cutoff estimate.
This supplies the low-zero term in the fourth-order smoothed estimate. -/
theorem rpow_cutoff_le_log_fourth {c x : ℝ} (hx : 0 < x) (hy : 2 ≤ Real.log x)
    (hsmall : 324 * Real.log (Real.log x) ^ 3 ≤ c * Real.log x) :
    x ^ (1 - c / Real.log ((Real.log x) ^ 8 + 2) ^ 2) ≤ x / (Real.log x) ^ 4 := by
  let y := Real.log x
  let L := Real.log (y ^ 8 + 2)
  have hy0 : 0 < y := (by norm_num only : (0 : ℝ) < 2).trans_le hy
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy] : 1 ≤ y)
  have hL0 : 0 < L :=
    Real.log_pos
      (by
        have h := pow_nonneg hy0.le 8
        linarith only [h])
  have hL := log_eighth_power_cutoff_le hy
  have hsq : L ^ 2 ≤ 81 * Real.log y ^ 2 := by
    change L ≤ 9 * Real.log y at hL
    nlinarith only [hL0, hL, sq_nonneg (9 * Real.log y - L)]
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * Real.log y by positivity)
  have hb : (4 * Real.log y) * L ^ 2 ≤ c * y := by
    change 324 * Real.log y ^ 3 ≤ c * y at hsmall
    nlinarith only [hm, hsmall]
  have hd : 4 * Real.log y ≤ c * y / L ^ 2 := (le_div_iff₀ (sq_pos_of_pos hL0)).mpr hb
  have he : x / y ^ 4 = Real.exp (Real.log x - 4 * Real.log y) := by
    rw [Real.exp_sub, Real.exp_log hx, mul_comm 4 (Real.log y), ← Real.rpow_def_of_pos hy0]
    rw [Real.rpow_ofNat]
  change x ^ (1 - c / L ^ 2) ≤ x / y ^ 4
  rw [he, Real.rpow_def_of_pos hx, Real.exp_le_exp]
  have hi : Real.log x * (1 - c / L ^ 2) = y - c * y / L ^ 2 := by
    dsimp only [y]; ring
  rw [hi]
  linarith only [hd]

/-- For every positive coefficient c, 324*log(y)^3 is eventually at most c*y.
Use logarithmic little-o with linear comparison. This verifies the saving needed
for the all-height zero-free cutoff without an explicit numerical entrance. -/
theorem eventually_log_cube_le_linear {c : ℝ} (hc : 0 < c) :
    ∀ᶠ y : ℝ in Filter.atTop, 324 * Real.log y ^ 3 ≤ c * y := by
  have h := ((isLittleO_log_rpow_rpow_atTop (3 : ℝ) zero_lt_one).const_mul_left (324 : ℝ)).bound hc
  filter_upwards [h, Filter.eventually_ge_atTop (2 : ℝ)] with y h hy
  have hy0 : 0 ≤ y := (by norm_num only : (0 : ℝ) ≤ 2).trans hy
  exact
    (le_abs_self _).trans
      (by simpa only [Real.rpow_ofNat, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hy0] using h)

/-- For positive y, the inverse-square-root tail at cutoff y^8 equals y to the
negative fourth power. Combine real powers and remove the natural exponent cast.
This matches the high-zero error to the low-zero fourth-order logarithmic saving. -/
theorem eighth_power_tail_eq {y : ℝ} (hy : 0 < y) : (y ^ 8) ^ (-(1 : ℝ) / 2) = 1 / y ^ 4 := by
  rw [← Real.rpow_ofNat y 8, ← Real.rpow_mul hy.le, show (8 : ℝ) * (-1 / 2) = -4 by norm_num only,
    Real.rpow_neg hy.le, Real.rpow_ofNat, one_div]

/-- For any nonnegative fixed coefficient A, A*(1+log x) is eventually bounded
by x/log(x)^4. Absorb the fifth power of one plus log x into x and compare powers.
This removes the fixed origin and trivial-zero corrections from the smoothed error. -/
theorem eventually_log_correction_le {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in Filter.atTop, A * (1 + Real.log x) ≤ x / Real.log x ^ 4 := by
  have ha := Analysis.eventually_mul_one_add_log_pow_lt_rpow hA zero_lt_one 5
  filter_upwards [ha, Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (2 : ℝ))] with x
    ha hx
  have hl : 0 < Real.log x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hp := pow_le_pow_left₀ hl.le (show Real.log x ≤ 1 + Real.log x by linarith only) 4
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hA (by positivity : 0 ≤ 1 + Real.log x))
  rw [Real.rpow_one] at ha
  apply (le_div_iff₀ (pow_pos hl 4)).mpr
  have he : A * (1 + Real.log x) * (1 + Real.log x) ^ 4 = A * (1 + Real.log x) ^ 5 := by ring
  rw [he] at hm
  exact hm.trans ha.le

end PseudoPrime.Analysis
