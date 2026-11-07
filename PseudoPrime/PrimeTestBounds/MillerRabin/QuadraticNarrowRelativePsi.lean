/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaRelativePsi

/-! # Narrow relative-width Chebyshev lower bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a relative width at most 1/32, the logarithmic secant retains the
fraction `1 - (32/63)h` of the interval. The trapezoid bound and positive
denominator yield the sharper coefficient required in the Gaussian comparison. -/
theorem relative_log_main_bound_32 {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 32) :
    (1 - (32 / 63 : ℝ) * h) * (-Real.log (1 - h)) ≤ h := by
  have hd : 0 < 2 * (1 - h) := by linarith only [hh1]
  have hb : 0 ≤ 1 - (32 / 63 : ℝ) * h := by linarith only [hh1]
  have hl := (relative_log_width_bounds hh (by linarith only [hh1])).2
  have hm := mul_le_mul_of_nonneg_left hl hb
  rw [← mul_div_assoc] at hm
  have hc := mul_nonneg (sq_nonneg h) (show 0 ≤ 1 / 32 - h by linarith only [hh1])
  have hs : (1 - (32 / 63 : ℝ) * h) * (h * (2 - h)) / (2 * (1 - h)) ≤ h := by
    apply (div_le_iff₀ hd).2
    nlinarith only [hc, hh, hh1]
  exact hm.trans hs

/-- Under RH, a relative-width secant with lower endpoint above one bounds
`psi(t)` from below using the explicit zero-mass constant. The trapezoid
estimate controls the main term and the linear logarithm bound controls the
zero contribution. This supplies the narrow-width Gaussian endpoint estimate. -/
theorem psi_relative_lower_large_32 (hRH : RiemannHypothesis) {h t : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1 / 32) (ht : 0 ≤ t) (ha : 1 < (1 - h) * t) :
    (1 - (32 / 63 : ℝ) * h) * t - (231 / 2500 : ℝ) * (Real.sqrt t + 1) / h - 1839 / 1000 ≤
      Chebyshev.psi t := by
  have hd : 0 < 1 - h := by linarith only [hh1]
  have ht0 : 0 < t := by nlinarith only [ha, hd, ht]
  have hat : (1 - h) * t < t := by nlinarith only [mul_pos hh ht0]
  have he : t / ((1 - h) * t) = (1 - h)⁻¹ := by
    apply (div_eq_iff (mul_ne_zero hd.ne' ht0.ne')).2
    rw [← mul_assoc, inv_mul_cancel₀ hd.ne', one_mul]
  have hw := relative_log_width_bounds hh.le (by linarith only [hh1])
  have hl : 0 < -Real.log (1 - h) := lt_of_lt_of_le hh hw.1
  have hs := psi_lower_log_secant hRH ha hat
  rw [he, Real.log_inv] at hs
  have hroot := Real.sqrt_le_sqrt hat.le
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
      (show 0 ≤ Real.sqrt ((1 - h) * t) + Real.sqrt t + 2 by
        linarith only [Real.sqrt_nonneg ((1 - h) * t), Real.sqrt_nonneg t])
  have hnum :
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass *
        (Real.sqrt ((1 - h) * t) + Real.sqrt t + 2) ≤
      (231 / 2500 : ℝ) * (Real.sqrt t + 1) := by
    nlinarith only [hm, hroot]
  have hnum0 : 0 ≤ (231 / 2500 : ℝ) * (Real.sqrt t + 1) :=
    mul_nonneg (by norm_num only) (by linarith only [Real.sqrt_nonneg t])
  have herr :=
    (div_le_div_of_nonneg_right hnum hl.le).trans (div_le_div_of_nonneg_left hnum0 hh hw.1)
  have hmain : (1 - (32 / 63 : ℝ) * h) * t ≤ (t - (1 - h) * t) / (-Real.log (1 - h)) := by
    apply (le_div_iff₀ hl).2
    have hm := mul_le_mul_of_nonneg_right (relative_log_main_bound_32 hh.le hh1) ht
    nlinarith only [hm]
  linarith only [hs, herr, hmain, Analysis.log_two_mul_pi_lt]

/-- Under RH, every nonnegative cutoff and relative width in `(0,1/32]`
satisfies the sharper one-sided Chebyshev bound used in the Gaussian comparison.
Use the logarithmic secant above one and nonnegativity of `psi` below it. -/
theorem psi_relative_lower_32 (hRH : RiemannHypothesis) {h t : ℝ} (hh : 0 < h) (hh1 : h ≤ 1 / 32)
    (ht : 0 ≤ t) :
    (1 - (32 / 63 : ℝ) * h) * t - (231 / 2500 : ℝ) * (Real.sqrt t + 1) / h - 1839 / 1000 ≤
      Chebyshev.psi t := by
  by_cases ha : 1 < (1 - h) * t
  · exact psi_relative_lower_large_32 hRH hh hh1 ht ha
  · have ht2 : t ≤ 2 := by
      have hm := mul_nonneg (show 0 ≤ 1 / 2 - h by linarith only [hh1]) ht
      nlinarith only [le_of_not_gt ha, hm]
    have he : (231 / 2500 : ℝ) ≤ (231 / 2500 : ℝ) * (Real.sqrt t + 1) := by
      nlinarith only [Real.sqrt_nonneg t]
    have he' : (231 / 250 : ℝ) ≤ (231 / 2500 : ℝ) * (Real.sqrt t + 1) / h := by
      apply (le_div_iff₀ hh).2
      nlinarith only [he, hh1]
    have hmain : (1 - (32 / 63 : ℝ) * h) * t ≤ 2 := by
      have hm := mul_nonneg hh.le ht
      nlinarith only [ht2, hm]
    linarith only [hmain, he', Chebyshev.psi_nonneg t]

end PseudoPrime.PrimeTestBounds.MillerRabin
