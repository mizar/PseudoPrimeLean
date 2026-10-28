/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SharpNormalForm
public import PseudoPrime.Analysis.GaussianSeededTunedOrder

/-! # Exact seeded normal form of the current sharp envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above scale 240 every current low-profile root exceeds 13.1.
The exact quadratic budget and residual floor 8.13 exclude a smaller root. -/
theorem gaussianLow_root_gt131 (f : Analysis.GaussianLowProfile) {L : ℝ} (hL : 240 ≤ L) :
    (131 / 10 : ℝ) < f.root L := by
  have hD : (813 / 100 : ℝ) ≤ f.residual := by
    cases f <;> norm_num only [Analysis.GaussianLowProfile.residual]
  have hp := f.root_pos L
  have hG := f.budget (by linarith only [hL] : (0 : ℝ) ≤ L)
  change _ ≤ Analysis.gaussianMRRefinedD * f.root L ^ 2 at hG
  by_contra hn
  have hr : f.root L ≤ (131 / 10 : ℝ) := le_of_not_gt hn
  have hfac :
    0 ≤ Analysis.gaussianMRRefinedD * (131 / 10 + f.root L) - Analysis.gaussianMRRefinedBeta := by
    have hd := mul_nonneg Analysis.gaussianMRRefined_coefficients.1.le hp.le
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint] at hd ⊢
    linarith only [hd]
  have hm := mul_nonneg (sub_nonneg.mpr hr) hfac
  norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedBeta,
    Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedWidth,
    Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint,
    Analysis.gaussianMRRefinedConductor] at hm hG
  nlinarith only [hm, hG, hL, hD]

/-- The old seeded 35000 profile is below each current Gaussian low profile
from scale 240. Its smaller residual controls the raw root and 13.1 controls its floor. -/
theorem seededSharp35_le_low (f : Analysis.GaussianLowProfile) {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianSeededSharpBound false L ≤ f.bound L := by
  have hr := gaussianLow_root_gt131 f hL
  have hp := f.root_pos L
  have hf : (35000 : ℝ) ≤ f.bound L := by
    have h2 := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 131 / 10) hp.le).mpr hr.le
    have h4 :=
      (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ (131 / 10) ^ 2) (sq_nonneg (f.root L))).mpr h2
    change _ ≤ (6 / 5 : ℝ) * (f.root L ^ 2) ^ 2
    nlinarith only [h4]
  have hD : Analysis.gaussianSeededSharpConstant false ≤ f.residual := by
    cases f <;>
      norm_num only [Analysis.gaussianSeededSharpConstant, Analysis.GaussianLowProfile.residual,
        Bool.false_eq_true, ite_false]
  have hraw : Analysis.gaussianSeededSharpRawRoot false L ≤ f.root L :=
    (Analysis.gaussianBudgetRoot_mono (b := Analysis.gaussianMRRefinedBeta)
          Analysis.gaussianMRRefined_coefficients.1
          (add_le_add (le_refl (Analysis.gaussianMRRefinedConductor * L)) hD)).trans
      (le_max_right _ _)
  have h2 := (sq_le_sq₀ (Analysis.gaussianSeededSharp_raw_pos false L).le hp.le).mpr hraw
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  rw [Analysis.gaussianSeededSharp_eq_max]
  apply max_le
  · exact hf
  · exact mul_le_mul_of_nonneg_left h4 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Above scale 240 the sharp seeded selection absorbs the full current Gaussian low family. -/
theorem seededSharp_le_lowFamily {L : ℝ} (hL : 240 ≤ L) :
    Analysis.gaussianSeededSharp L ≤ Analysis.gaussianLowFamily L := by
  rw [Analysis.gaussianSeededSharp_eq_min (by linarith only [hL])]
  exact
    (min_le_left _ _).trans
      (le_min (seededSharp35_le_low .low hL)
        (le_min (seededSharp35_le_low .middle hL) (seededSharp35_le_low .upper hL)))

/-- At scales [240,3e10), the current sharp public selection is exactly its seeded family.
Use the normal form, Gaussian absorption and the pointwise comparison. -/
theorem sharpSelected_eq_seeded {n : ℕ} (hN : 3000 ≤ n) (hL : 240 ≤ Real.log n)
    (hU : Real.log n < 30000000000) :
    sharpSelectedEnvelope n = Analysis.gaussianSeededSharp (Real.log n) := by
  have hg := seededSharp_le_lowFamily hL
  have hp := hg.trans (gaussianLowFamily_lt_pointwise (by linarith only [hL])).le
  rw [sharpSelected_eq_regular hN hU, lowFinitePointwise_eq_pointwise (by linarith only [hL]),
    min_eq_right hg, min_eq_right hp]

end PseudoPrime.PrimeTestBounds.MillerRabin
