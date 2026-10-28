/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianTunedOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpNormalForm

/-! # Tuned Gaussian improvements over the complete sharp envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The tuned upper component remains strictly below the unchanged prefix floor through 235.73.
A rational root test at 13.0683 gives a continuous certificate, including the endpoint. -/
theorem gaussianTunedUpper_lt35000 {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 23573 / 100) :
    Analysis.GaussianTunedProfile.upper.bound L < (35000 : ℝ) := by
  have hC : 0 ≤ Analysis.gaussianMRRefinedConductor * L + 65 / 8 := by
    norm_num only [Analysis.gaussianMRRefinedConductor]
    linarith only [hL]
  have hcoef : Analysis.gaussianMRRefinedBeta < Analysis.gaussianMRRefinedD * (130683 / 10000) := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedMass,
      Analysis.gaussianMRRefinedBeta, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint]
  have hbudget :
    Analysis.gaussianMRRefinedConductor * L + 65 / 8 +
        Analysis.gaussianMRRefinedBeta * (130683 / 10000) <
      Analysis.gaussianMRRefinedD * (130683 / 10000 : ℝ) ^ 2 := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedConductor,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedWidth, Analysis.gaussianMR6FifthsIndex,
      Analysis.gaussianMR6FifthsEndpoint]
    linarith only [hU]
  have hraw :=
    lowGaussian_root_lt Analysis.gaussianMRRefined_coefficients.1
      Analysis.gaussianMRRefined_coefficients.2 hC hcoef hbudget
  have hroot : Analysis.GaussianTunedProfile.upper.root L < (130683 / 10000 : ℝ) :=
    max_lt (by norm_num only [Analysis.GaussianTunedProfile.floor]) hraw
  have hp := Analysis.GaussianTunedProfile.root_pos .upper L
  have hs := (sq_lt_sq₀ hp.le (by norm_num only : (0 : ℝ) ≤ 130683 / 10000)).mpr hroot
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ (130683 / 10000) ^ 2)).mpr hs
  change (6 / 5 : ℝ) * (Analysis.GaussianTunedProfile.upper.root L ^ 2) ^ 2 < 35000
  nlinarith only [hs']

/-- The tuned family lies below 35000 through the closed extended endpoint. -/
theorem gaussianTunedFamily_lt35000 {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 23573 / 100) :
    Analysis.gaussianTunedFamily L < (35000 : ℝ) :=
  (Analysis.gaussianTunedFamily_le .upper L).trans_lt (gaussianTunedUpper_lt35000 hL hU)

/-- The tuned family strictly improves the complete sharp selection on [100,235.73].
Use its strict comparison to the old Gaussian family, its extended 35000 certificate,
and the old family's pointwise comparison in the normal form of the sharp envelope. -/
theorem gaussianTunedFamily_lt_sharp {n : ℕ} (hN : 3000 ≤ n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 23573 / 100) :
    Analysis.gaussianTunedFamily (Real.log n) < sharpSelectedEnvelope n := by
  have hG := Analysis.gaussianTunedFamily_lt_lowFamily hL
  have hP := hG.trans (gaussianLowFamily_lt_pointwise hL)
  have hS :=
    (gaussianTunedFamily_lt35000 (by linarith only [hL]) hU).trans_le
      (Analysis.gaussianSeededSharp_floor (Real.log n))
  rw [sharpSelected_eq_regular hN (by linarith only [hU]),
    lowFinitePointwise_eq_pointwise (by linarith only [hL])]
  exact lt_min hP (lt_min hG hS)

/-- Through scale 110, the new bridge root remains strictly below the old middle floor. -/
theorem gaussianTunedBridge_lt_floor {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 110) :
    Analysis.GaussianTunedProfile.bridge.bound L < (6 / 5 : ℝ) * ((19 / 2 : ℝ) ^ 2) ^ 2 := by
  have hC : 0 ≤ Analysis.gaussianMRRefinedConductor * L + 87 / 10 := by
    norm_num only [Analysis.gaussianMRRefinedConductor]
    linarith only [hL]
  have hcoef : Analysis.gaussianMRRefinedBeta < Analysis.gaussianMRRefinedD * (19 / 2) := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedMass,
      Analysis.gaussianMRRefinedBeta, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint]
  have hbudget :
    Analysis.gaussianMRRefinedConductor * L + 87 / 10 + Analysis.gaussianMRRefinedBeta * (19 / 2) <
      Analysis.gaussianMRRefinedD * (19 / 2 : ℝ) ^ 2 := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedMass,
      Analysis.gaussianMRRefinedBeta, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint,
      Analysis.gaussianMRRefinedConductor]
    linarith only [hU]
  have hraw :=
    lowGaussian_root_lt Analysis.gaussianMRRefined_coefficients.1
      Analysis.gaussianMRRefined_coefficients.2 hC hcoef hbudget
  have hroot : Analysis.GaussianTunedProfile.bridge.root L < (19 / 2 : ℝ) :=
    max_lt (by norm_num only [Analysis.GaussianTunedProfile.floor]) hraw
  have hs :=
    (sq_lt_sq₀ (Analysis.GaussianTunedProfile.root_pos .bridge L).le
          (by norm_num only : (0 : ℝ) ≤ 19 / 2)).mpr
      hroot
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
  exact mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5)

/-- With the original prefix alone, the low and bridge candidates improve the old family
throughout the full closed interval [100,110]. -/
theorem gaussianTunedEarly_lt_lowFamily {L : ℝ} (hL : 100 ≤ L) (hU : L ≤ 110) :
    Analysis.gaussianTunedEarlyFamily L < Analysis.gaussianLowFamily L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hsecond : L ≤ Analysis.gaussianLowSwitch (49 / 5) (163 / 20) := by
    have hsw : (110 : ℝ) ≤ Analysis.gaussianLowSwitch (49 / 5) (163 / 20) := by
      norm_num only [Analysis.gaussianLowSwitch, Analysis.gaussianMRRefinedD,
        Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedBeta,
        Analysis.gaussianMRRefinedWidth, Analysis.gaussianMR6FifthsIndex,
        Analysis.gaussianMR6FifthsEndpoint, Analysis.gaussianMRRefinedConductor]
    exact hU.trans hsw
  rw [Analysis.gaussianLowFamily_selection h0]
  by_cases hfirst : L ≤ Analysis.gaussianLowSwitch (19 / 2) (93 / 10)
  · rw [ite_eq_left hfirst]
    exact (min_le_left _ _).trans_lt (Analysis.gaussianTunedLow_lt_low hL)
  · rw [ite_eq_right hfirst, ite_eq_left hsecond]
    have hm : (19 / 2 : ℝ) ≤ Analysis.GaussianLowProfile.middle.root L :=
      Analysis.GaussianLowProfile.root_floor .middle L
    have hs :=
      (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 19 / 2)
            (Analysis.GaussianLowProfile.root_pos .middle L).le).mpr
        hm
    have hs' := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
    have hb := mul_le_mul_of_nonneg_left hs' (by norm_num only : (0 : ℝ) ≤ 6 / 5)
    exact (min_le_right _ _).trans_lt ((gaussianTunedBridge_lt_floor h0 hU).trans_le hb)

/-- The old-prefix early family improves the complete sharp selection on [100,110]. -/
theorem gaussianTunedEarly_lt_sharp {n : ℕ} (hN : 3000 ≤ n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 110) :
    Analysis.gaussianTunedEarlyFamily (Real.log n) < sharpSelectedEnvelope n := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hG := gaussianTunedEarly_lt_lowFamily hL hU
  have hP := hG.trans (gaussianLowFamily_lt_pointwise hL)
  have hB : Analysis.gaussianTunedEarlyFamily (Real.log n) < (6 / 5 : ℝ) * ((19 / 2 : ℝ) ^ 2) ^ 2 :=
    (min_le_right _ _).trans_lt (gaussianTunedBridge_lt_floor h0 hU)
  have h35 : Analysis.gaussianTunedEarlyFamily (Real.log n) < (35000 : ℝ) :=
    hB.trans (by norm_num only)
  have hS := h35.trans_le (Analysis.gaussianSeededSharp_floor (Real.log n))
  rw [sharpSelected_eq_regular hN (by linarith only [hU]),
    lowFinitePointwise_eq_pointwise (by linarith only [hL])]
  exact lt_min hP (lt_min hG hS)

end PseudoPrime.PrimeTestBounds.MillerRabin
