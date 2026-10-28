/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedIntervalSelection

/-! # Dominance of the current seeded profiles on the high analytic interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For logarithmic scale at least 240, the current raw35 root is at least thirteen.
Use the exact quadratic equation and factor its difference at thirteen. -/
theorem currentSeeded_raw13 {L : ℝ} (hL : 240 ≤ L) :
    (13 : ℝ) ≤ Analysis.gaussianRecoveredSeededRawRoot false L := by
  let s := Analysis.gaussianRecoveredSeededRawRoot false L
  have hs : 0 < s := Analysis.gaussianRecoveredSeeded_raw_pos false L
  have he :=
    Analysis.gaussianRecoveredSeeded_raw_equation false (by linarith only [hL] : (0 : ℝ) ≤ L)
  change
    Analysis.gaussianMRRefinedD * s ^ 2 =
      Analysis.gaussianMRRefinedConductor * L + Analysis.gaussianMRRefinedBeta * s +
        Analysis.gaussianRecoveredSeededConstant false at he
  by_contra hn
  have hlt : s < 13 := lt_of_not_ge hn
  have ha : 0 < 13 * Analysis.gaussianMRRefinedD - Analysis.gaussianMRRefinedBeta := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsEndpoint, Analysis.gaussianMR6FifthsIndex]
  have hm :=
    mul_nonneg (sub_nonneg.mpr hlt.le)
      (show 0 ≤ Analysis.gaussianMRRefinedD * (13 + s) - Analysis.gaussianMRRefinedBeta
        by
        have hd := mul_nonneg Analysis.gaussianMRRefined_coefficients.1.le hs.le
        linarith only [ha, hd])
  norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedBeta,
    Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedWidth,
    Analysis.gaussianMR6FifthsEndpoint, Analysis.gaussianMR6FifthsIndex,
    Analysis.gaussianMRRefinedConductor, Analysis.gaussianRecoveredSeededConstant,
    Bool.false_eq_true, ite_false] at he hm
  nlinarith only [he, hm, hL]

/-- For logarithmic scale at least 240, the current raw35 radius is at most 18L/25.
Use the root lower anchor to absorb its linear term in the exact budget equation. -/
theorem currentSeeded_raw_radius {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianRecoveredSeededRawRoot false L ^ 2 ≤ (18 / 25 : ℝ) * L := by
  let s := Analysis.gaussianRecoveredSeededRawRoot false L
  have hs : (13 : ℝ) ≤ s := currentSeeded_raw13 hL
  have he :=
    Analysis.gaussianRecoveredSeeded_raw_equation false (by linarith only [hL] : (0 : ℝ) ≤ L)
  change
    Analysis.gaussianMRRefinedD * s ^ 2 =
      Analysis.gaussianMRRefinedConductor * L + Analysis.gaussianMRRefinedBeta * s +
        Analysis.gaussianRecoveredSeededConstant false at he
  have hm := mul_nonneg (by linarith only [hs] : (0 : ℝ) ≤ s) (sub_nonneg.mpr hs)
  norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedBeta,
    Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedWidth,
    Analysis.gaussianMR6FifthsEndpoint, Analysis.gaussianMR6FifthsIndex,
    Analysis.gaussianMRRefinedConductor, Analysis.gaussianRecoveredSeededConstant,
    Bool.false_eq_true, ite_false] at he
  change s ^ 2 ≤ (18 / 25 : ℝ) * L
  nlinarith only [he, hm, hL]

/-- Above scale 240, the current selected seeded cutoff is at most (1944/3125)L squared.
Bound the raw35 radius and its fixed 35000 floor before taking the profile minimum. -/
theorem currentSeeded_quadratic {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianRecoveredSeeded L ≤ (1944 / 3125 : ℝ) * L ^ 2 := by
  have h63 : (63 : ℝ) ≤ L := by linarith only [hL]
  rw [Analysis.gaussianRecoveredSeeded_eq_min h63]
  apply (min_le_left _ _).trans
  rw [Analysis.gaussianRecoveredSeeded_eq_max]
  apply max_le
  · norm_num only [Analysis.gaussianRecoveredSeededCutoff, Bool.false_eq_true, ite_false,
      Nat.cast_ofNat]
    nlinarith only [hL, sq_nonneg (L - 240)]
  · have hr := currentSeeded_raw_radius hL
    have hs := (sq_le_sq₀ (sq_nonneg _) (by linarith only [hL] : (0 : ℝ) ≤ (18 / 25) * L)).mpr hr
    change (6 / 5 : ℝ) * (Analysis.gaussianRecoveredSeededRawRoot false L ^ 2) ^ 2 ≤ _
    nlinarith only [hs]

/-- Above scale 240, the current selected seeded cutoff is below the current Gamma cutoff.
Drop the positive terms in the Gamma gap equation and compare the resulting quadratic constants. -/
theorem currentSeeded_le_gamma {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianRecoveredSeeded L ≤ gammaRecoveredBound L := by
  let r := gammaRecoveredRoot L
  have h101 : (101 : ℝ) ≤ L := by linarith only [hL]
  have hr : 0 < r := gammaRecoveredRoot_pos h101
  have he := gammaRecoveredGap_root_eq_zero h101
  have hp : 0 < ((7 / 6 : ℝ) * L + 58129633 / 2223000) / r := div_pos (by linarith only [hL]) hr
  change gammaRecoveredGap L r = 0 at he
  dsimp only [gammaRecoveredGap] at he
  have hlin : ((11783423 / 25000000 : ℝ) / (86733 / 98800)) * L < r := by
    norm_num only at he ⊢
    linarith only [he, hp]
  have hpos : (0 : ℝ) ≤ ((11783423 / 25000000 : ℝ) / (86733 / 98800)) * L := by
    norm_num only
    linarith only [hL]
  have hs := (sq_lt_sq₀ hpos hr.le).mpr hlin
  have hq := currentSeeded_quadratic hL
  change _ ≤ (99 / 40 : ℝ) * r ^ 2
  norm_num only at hs
  nlinarith only [hs, hq, sq_pos_of_pos (by linarith only [hL] : (0 : ℝ) < L)]

/-- Above scale 240, the current selected seeded cutoff is below the current Gaussian1000 cutoff.
Compare residual allowances in the common quadratic root and check coverage of the 35000 floor. -/
theorem currentSeeded_le_gaussian {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianRecoveredSeeded L ≤ Analysis.gaussianRecoveredBound L := by
  let s := Analysis.gaussianRecoveredRoot L
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hs := Analysis.gaussianRecovered_root_ten L
  change (10 : ℝ) ≤ s at hs
  have hG := Analysis.gaussianRecovered_large_budget h0
  change
    Analysis.gaussianMRRefinedConductor * L + Analysis.gaussianMRRefinedBeta * s + 407 / 50 ≤
      Analysis.gaussianMRRefinedD * s ^ 2 at hG
  have h13 : (131 / 10 : ℝ) ≤ s := by
    by_contra hn
    have ht : s < 131 / 10 := lt_of_not_ge hn
    have hm := mul_nonneg (sub_nonneg.mpr ht.le) (by linarith only [hs] : 0 ≤ s + 131 / 10)
    norm_num only [Analysis.gaussianMRRefinedConductor, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsEndpoint, Analysis.gaussianMR6FifthsIndex] at hG
    nlinarith only [hG, hs, hm, hL]
  have hraw : Analysis.gaussianRecoveredSeededRawRoot false L ≤ s := by
    change
      Analysis.gaussianBudgetRoot Analysis.gaussianMRRefinedD Analysis.gaussianMRRefinedBeta
          (Analysis.gaussianMRRefinedConductor * L +
            Analysis.gaussianRecoveredSeededConstant false) ≤
        s
    apply
      Analysis.gaussianBudgetRoot_le_of_budget Analysis.gaussianMRRefined_coefficients.1
        Analysis.gaussianMRRefined_coefficients.2
    · norm_num only [Analysis.gaussianMRRefinedConductor, Analysis.gaussianRecoveredSeededConstant,
        Bool.false_eq_true, ite_false]
      linarith only [hL]
    · have hm := mul_le_mul_of_nonneg_left h13 Analysis.gaussianMRRefined_coefficients.1.le
      norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedBeta,
        Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedWidth,
        Analysis.gaussianMR6FifthsEndpoint, Analysis.gaussianMR6FifthsIndex] at hm ⊢
      linarith only [hm]
    · norm_num only [Analysis.gaussianRecoveredSeededConstant, Bool.false_eq_true, ite_false]
      linarith only [hG]
  rw [Analysis.gaussianRecoveredSeeded_eq_min (by linarith only [hL])]
  apply (min_le_left _ _).trans
  rw [Analysis.gaussianRecoveredSeeded_eq_max]
  apply max_le
  · norm_num only [Analysis.gaussianRecoveredSeededCutoff, Bool.false_eq_true, ite_false,
      Nat.cast_ofNat]
    change (35000 : ℝ) ≤ (6 / 5 : ℝ) * (s ^ 2) ^ 2
    have hs2 :=
      (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 131 / 10) (by linarith only [h13] : (0 : ℝ) ≤ s)).mpr
        h13
    have hs4 := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ (131 / 10) ^ 2) (sq_nonneg s)).mpr hs2
    nlinarith only [hs4]
  · have hs2 :=
      (sq_le_sq₀ (Analysis.gaussianRecoveredSeeded_raw_pos false L).le
            (by linarith only [hs] : (0 : ℝ) ≤ s)).mpr
        hraw
    have hs4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg s)).mpr hs2
    change
      (6 / 5 : ℝ) * (Analysis.gaussianRecoveredSeededRawRoot false L ^ 2) ^ 2 ≤
        (6 / 5 : ℝ) * (s ^ 2) ^ 2
    linarith only [hs4]

/-- For inputs above one with scale in [240,1.1 trillion), the current refined selection
equals its current seeded candidate. Compare every competing candidate in the analytic formula. -/
theorem refinedSelected_eq_currentSeeded {n : ℕ} (hn : 1 < n) (hL : 240 ≤ Real.log n)
    (hU : Real.log n < 1100000000000) :
    refinedSelectedEnvelope n = Analysis.gaussianRecoveredSeeded (Real.log n) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hb : Analysis.gaussianRecoveredSeeded (Real.log n) ≤ lowPrimeTightSelected n := by
    rw [← lowPrimeTight_eq_selected hn, lowPrimeTight_eq_next_of_log (by linarith only [hL]),
      next_eq_seeded hn hL (by linarith only [hU])]
    exact Analysis.gaussianRecoveredSeeded_le_seeded h63
  rw [refinedSelected_eq_analytic (by linarith only [hL]) hU,
    min_eq_right (currentSeeded_le_gamma hL), min_eq_right (currentSeeded_le_gaussian hL),
    min_eq_right hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
