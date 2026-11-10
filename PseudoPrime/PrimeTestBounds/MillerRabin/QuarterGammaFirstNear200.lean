/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaFirstRange

/-! # First Gamma correction near radius 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem gamma_exp_low_check :
    1340000 ≤ Analysis.expFixedPointSignedLowerFast (-529) 80 1000000000 64 := by decide +kernel

private theorem gamma_exp_high_check :
    2110000000000 ≤ Analysis.expFixedPointSignedLowerFast 957 125 1000000000 64 := by decide +kernel

private theorem gamma_exp_low : (134 / 100000 : ℝ) ≤ Real.exp (-(529 / 80 : ℝ)) := by
  have h :=
    Analysis.exp_fixed_signed_lower_div (-529) 80 1000000000 64 (by norm_num only)
      (by norm_num only) (by norm_num only)
  have hcheck := gamma_exp_low_check
  rw [Analysis.expFixedPointSignedLowerFast_eq] at hcheck
  have hc : (1340000 : ℝ) ≤ (Analysis.expFixedPointSignedLower (-529) 80 1000000000 64 : ℝ) := by
    exact_mod_cast hcheck
  norm_num only at h ⊢
  linarith only [h, hc]

private theorem gamma_exp_high : Real.exp (-(957 / 125 : ℝ)) ≤ 474 / 1000000 := by
  have hcheck := gamma_exp_high_check
  rw [Analysis.expFixedPointSignedLowerFast_eq] at hcheck
  have hp : 0 < Analysis.expFixedPointSignedLower 957 125 1000000000 64 :=
    lt_of_lt_of_le (by norm_num only) hcheck
  have h :=
    Analysis.exp_upper_of_signed_fixed_lower (-957) 125 1000000000 64 (by norm_num only)
      (by norm_num only) (by norm_num only) (by simpa only [neg_neg] using hp)
  have hc :
    (2110000000000 : ℝ) ≤ (Analysis.expFixedPointSignedLower 957 125 1000000000 64 : ℝ) := by
    exact_mod_cast hcheck
  norm_num only at h ⊢
  have hpos : 0 < (Analysis.expFixedPointSignedLower 957 125 1000000000 64 : ℝ) := by
    exact_mod_cast hp
  apply h.trans
  apply (div_le_iff₀ hpos).2
  nlinarith only [hc]

private theorem quarter_first_correction_sharp {z : ℝ} (hz : (66 / 5 : ℝ) ≤ z) (hZ : z ≤ 529 / 40) :
    (1 / 25 : ℝ) ≤ quarterGammaFirstCorrection z := by
  have h := quarter_first_correction_interval (a := 66 / 5) (b := 529 / 40) (by norm_num only) hz hZ
  have hpoly : 0 ≤ Analysis.logPowerTailPoly (29 / 50 : ℝ) 5 (66 / 5) := by
    norm_num only [Analysis.logPowerTailPoly]
  have hm := mul_le_mul_of_nonneg_right gamma_exp_high hpoly
  have hM :
    Analysis.logPowerTailPoly (29 / 50 : ℝ) 5 0 -
        (474 / 1000000 : ℝ) * Analysis.logPowerTailPoly (29 / 50) 5 (66 / 5) ≤
      Analysis.logPowerTailPoly (29 / 50 : ℝ) 5 0 -
        Real.exp (-(957 / 125 : ℝ)) * Analysis.logPowerTailPoly (29 / 50) 5 (66 / 5) := by
    linarith only [hm]
  have hM0 :
    0 ≤
      Analysis.logPowerTailPoly (29 / 50 : ℝ) 5 0 -
        (474 / 1000000 : ℝ) * Analysis.logPowerTailPoly (29 / 50) 5 (66 / 5) := by
    norm_num only [Analysis.logPowerTailPoly]
  have hp := mul_le_mul gamma_exp_low hM hM0 (Real.exp_pos _).le
  have hs := mul_le_mul_of_nonneg_left hp (show 0 ≤ (27 / 25 : ℝ) ^ 5 / 120 by positivity)
  norm_num only [Analysis.logPowerTailPoly] at hs h ⊢
  linarith only [hs, h]

private theorem gamma_log_range_checks :
    Analysis.rationalLogIntervalCheck 39601 15 32 (423 / 40) 11 = true ∧
      Analysis.rationalLogIntervalCheck 40000 15 32 10 (53 / 5) = true := by
  decide +kernel

/-- On radii from 199 through 200, the first Gamma correction is at least 1/25.
Rational endpoint checks and the monotone moment bound give the estimate. -/
theorem quarter_first_correction_199_200 {r : ℝ} (hr : 199 ≤ r) (hR : r ≤ 200) :
    (1 / 25 : ℝ) ≤ quarterGammaFirstCorrection (Real.log (r ^ 2) + 21 / 8) := by
  have hl := (Analysis.rationalLogIntervalCheck_sound gamma_log_range_checks.1).1
  have hu := (Analysis.rationalLogIntervalCheck_sound gamma_log_range_checks.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hu
  have hmin : (39601 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hmax : r ^ 2 ≤ (40000 : ℝ) := by nlinarith only [hr, hR]
  have hlogl := Real.log_le_log (by norm_num only : (0 : ℝ) < 39601) hmin
  have hlogu := Real.log_le_log (sq_pos_of_pos (by linarith only [hr])) hmax
  apply quarter_first_correction_sharp
  · linarith only [hl, hlogl]
  · linarith only [hu, hlogu]

end PseudoPrime.PrimeTestBounds.MillerRabin
