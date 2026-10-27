/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaProfileScaleGeometry
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Certified lower endpoints of the initial logarithmic profile ranges -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On L at least 100 log ten, L is at least 460517/2000.
Use the existing certified logarithms of two and five with log ten's
product identity. This fixes a rational anchor near the actual lower input. -/
theorem gamma_initial_profile_log_lower {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (460517 / 2000 : ℝ) ≤ L := by
  rw [Real.log_ten_eq] at hL
  linarith only [hL, Real.log_two_gt_d9, Real.log_five_gt_d9]

/-- On the same range, log L is at least 6799/1250.
Certify the logarithm of the rational anchor by a finite Taylor check,
then use monotonicity. This gives sharper initial scale endpoints. -/
theorem gamma_initial_profile_log_log_lower {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (6799 / 1250 : ℝ) ≤ Real.log L := by
  have ha :=
    (rationalLogIntervalCheck_sound
        (show rationalLogIntervalCheck (460517 / 2000) 8 32 (6799 / 1250) 6 = true by
          decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at ha
  exact ha.trans (Real.log_le_log (by norm_num only) (gamma_initial_profile_log_lower hL))

/-- The shift-twelve scale is at least 20712 throughout the input range.
Square the positive rational shifted-root lower bound. This proves the
lower endpoint required by the first shift-twelve cell without a new hypothesis. -/
theorem gamma_profile_twelve_scale_ge_initial {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (20712 : ℝ) ≤ gammaTailProfileScale L 12 := by
  have ht : (2531369 / 10000 : ℝ) ≤ L + 2 * Real.log L + 12 := by
    linarith only [gamma_initial_profile_log_lower hL, gamma_initial_profile_log_log_lower hL]
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 2531369 / 10000) (by linarith only [ht])).mpr ht
  dsimp only [gammaTailProfileScale]
  nlinarith only [hs]

/-- The shift-ten scale is at least 20386 throughout the same input range.
Use the same sharpened logarithmic anchors. This justifies the lower endpoint
of the already certified shift-ten initial cell. -/
theorem gamma_refined_scale_ge_initial {L : ℝ} (hL : 100 * Real.log 10 ≤ L) :
    (20386 : ℝ) ≤ gammaRefinedScale L := by
  have ht : (2511369 / 10000 : ℝ) ≤ L + 2 * Real.log L + 10 := by
    linarith only [gamma_initial_profile_log_lower hL, gamma_initial_profile_log_log_lower hL]
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 2511369 / 10000) (by linarith only [ht])).mpr ht
  dsimp only [gammaRefinedScale]
  nlinarith only [hs]

end PseudoPrime.Analysis
