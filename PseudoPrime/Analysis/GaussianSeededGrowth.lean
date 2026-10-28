/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRSeededComparison
public import PseudoPrime.Analysis.GaussianMR1000Numerics

/-! # Seeded Gaussian growth comparisons for interval selection -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- From L>=240 the raw seeded 35000 root has square at most (73/100)L. -/
theorem gaussianSeeded_raw_linear {L : ℝ} (hL : 240 ≤ L) :
    gaussianSeededRawRoot false L ^ 2 ≤ (73 / 100 : ℝ) * L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have harg : (0 : ℝ) ≤ (73 / 100) * L := mul_nonneg (by norm_num only) h0
  have hrlo : (13 : ℝ) ≤ Real.sqrt ((73 / 100 : ℝ) * L) :=
    (Real.le_sqrt (by norm_num only) harg).mpr (by linarith only [hL])
  have hrhi : Real.sqrt ((73 / 100 : ℝ) * L) ≤ L / 18 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by linarith only [hL], ?_⟩
    have hp := mul_nonneg h0 (sub_nonneg.mpr hL)
    nlinarith only [hp, hL]
  have hr2 := Real.sq_sqrt harg
  have hc : 0 ≤ gaussianMRRefinedConductor * L + gaussianSeededConstant false := by
    exact
      add_nonneg (mul_nonneg (by norm_num only [gaussianMRRefinedConductor]) h0)
        (gaussianSeeded_constant_pos false).le
  have hr : gaussianSeededRawRoot false L ≤ Real.sqrt ((73 / 100 : ℝ) * L) := by
    apply
      gaussianBudgetRoot_le_of_budget gaussianMRRefined_coefficients.1
        gaussianMRRefined_coefficients.2 hc
    · norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
      linarith only [hrlo]
    · norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
        gaussianMRRefinedConductor, gaussianSeededConstant, Bool.false_eq_true, ite_false]
      nlinarith only [hrhi, hr2, hL]
  exact ((sq_le_sq₀ (gaussianSeeded_raw_pos false L).le (Real.sqrt_nonneg _)).mpr hr).trans_eq hr2

/-- From L>=240 the selected seeded cutoff is strictly below (16/25)L^2. -/
theorem gaussianSeededSelected_linear {L : ℝ} (hL : 240 ≤ L) :
    gaussianSeededSelected L < (16 / 25 : ℝ) * L ^ 2 := by
  have hs : gaussianSeededSelected L ≤ gaussianSeededBound false L := by
    rw [← gaussianSeeded_min_eq_selected (by linarith only [hL])]
    exact min_le_left _ _
  apply hs.trans_lt
  rw [gaussianSeeded_eq_max]
  apply max_lt
  · norm_num only [gaussianSeededCutoff, Bool.false_eq_true, ite_false, Nat.cast_ofNat]
    nlinarith only [hL]
  · have hr := gaussianSeeded_raw_linear hL
    have hs :=
      (sq_le_sq₀ (sq_nonneg (gaussianSeededRawRoot false L))
            (by linarith only [hL] : (0 : ℝ) ≤ (73 / 100) * L)).mpr
        hr
    dsimp only [gaussianSeededRawBound]
    have hp : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
    nlinarith only [hs, hp]

/-- From L>=240 the large-index 1000-prefix root exceeds 13.1. -/
theorem gaussian1000_large_above {L : ℝ} (hL : 240 ≤ L) :
    (131 / 10 : ℝ) < gaussian1000LargeRoot L := by
  by_contra hn
  have h0 : (0 : ℝ) ≤ gaussianMRRefinedConductor * L + 163 / 20 := by
    norm_num only [gaussianMRRefinedConductor]
    linarith only [hL]
  have hb : gaussianMRRefinedBeta < gaussianMRRefinedD * (131 / 10) := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  have h :=
    gaussianBudget_of_root_le gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2 h0
      hb (le_of_not_gt hn)
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint,
    gaussianMRRefinedConductor] at h
  linarith only [hL, h]

/-- From L>=240 the seeded selected cutoff is below the two-root 1000-prefix cutoff. -/
theorem gaussianSeeded_lt_1000 {L : ℝ} (hL : 240 ≤ L) :
    gaussianSeededSelected L < gaussian1000Bound L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hp := gaussian1000_large_pos L
  have hroot : gaussianSeededRawRoot false L < gaussian1000LargeRoot L := by
    apply gaussianBudgetRoot_strictMono gaussianMRRefined_coefficients.1
    · exact
        add_nonneg (mul_nonneg (by norm_num only [gaussianMRRefinedConductor]) h0)
          (gaussianSeeded_constant_pos false).le
    · norm_num only [gaussianSeededConstant, Bool.false_eq_true, ite_false]
      linarith only
  have hsq := (sq_lt_sq₀ (gaussianSeeded_raw_pos false L).le hp.le).mpr hroot
  have hfour := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hsq
  have hraw : gaussianSeededRawBound false L < (6 / 5 : ℝ) * (gaussian1000LargeRoot L ^ 2) ^ 2 :=
    mul_lt_mul_of_pos_left hfour (by norm_num only)
  have hl := gaussian1000_large_above hL
  have hl2 := (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 131 / 10) hp.le).mpr hl
  have hl4 := (sq_lt_sq₀ (sq_nonneg (131 / 10 : ℝ)) (sq_nonneg (gaussian1000LargeRoot L))).mpr hl2
  have hfloor : (35000 : ℝ) < (6 / 5) * (gaussian1000LargeRoot L ^ 2) ^ 2 := by nlinarith only [hl4]
  have hrootle : gaussian1000LargeRoot L ≤ gaussian1000Root L :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hs2 := (sq_le_sq₀ hp.le (gaussian1000_root_pos L).le).mpr hrootle
  have hs4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs2
  have hcut : (6 / 5 : ℝ) * (gaussian1000LargeRoot L ^ 2) ^ 2 ≤ gaussian1000Bound L :=
    mul_le_mul_of_nonneg_left hs4 (by norm_num only)
  have hs : gaussianSeededSelected L ≤ gaussianSeededBound false L := by
    rw [← gaussianSeeded_min_eq_selected (by linarith only [hL])]
    exact min_le_left _ _
  apply hs.trans_lt
  rw [gaussianSeeded_eq_max]
  norm_num only [gaussianSeededCutoff, Bool.false_eq_true, ite_false, Nat.cast_ofNat]
  exact (max_lt hfloor hraw).trans_le hcut

end PseudoPrime.Analysis
