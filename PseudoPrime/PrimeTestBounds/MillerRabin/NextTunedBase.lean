/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TunedEnvelopeOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTunedAbsorption
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededTunedSelection

/-! # Exact base-envelope forms for further witness improvements -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At logarithmic scales at least 240, all four tuned Gaussian roots exceed 13.1.
Their certified budgets and the common residual floor exclude any smaller root. -/
theorem gaussianTuned_root_gt131 (f : GaussianTunedProfile) {L : ℝ} (hL : 240 ≤ L) :
    (131 / 10 : ℝ) < f.root L := by
  have hD : (65 / 8 : ℝ) ≤ f.residual := by
    cases f <;> norm_num only [GaussianTunedProfile.residual]
  have hp := f.root_pos L
  have hG := f.budget (by linarith only [hL] : (0 : ℝ) ≤ L)
  change _ ≤ gaussianMRRefinedD * f.root L ^ 2 at hG
  by_contra hn
  have hr : f.root L ≤ (131 / 10 : ℝ) := le_of_not_gt hn
  have hfac : 0 ≤ gaussianMRRefinedD * (131 / 10 + f.root L) - gaussianMRRefinedBeta := by
    have hd := mul_nonneg gaussianMRRefined_coefficients.1.le hp.le
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint] at hd ⊢
    linarith only [hd]
  have hm := mul_nonneg (sub_nonneg.mpr hr) hfac
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint,
    gaussianMRRefinedConductor] at hm hG
  nlinarith only [hm, hG, hL, hD]

/-- The tuned 35000 seeded cutoff lies below every four-profile Gaussian cutoff above scale 240.
Compare raw budgets and control the retained prefix floor by the root lower bound. -/
theorem seededTuned35_le_gaussian (f : GaussianTunedProfile) {L : ℝ} (hL : 240 ≤ L) :
    gaussianSeededTunedBound false L ≤ f.bound L := by
  have hr := gaussianTuned_root_gt131 f hL
  have hp := f.root_pos L
  have hf : (35000 : ℝ) ≤ f.bound L := by
    have h2 := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 131 / 10) hp.le).mpr hr.le
    have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
    change _ ≤ (6 / 5 : ℝ) * (f.root L ^ 2) ^ 2
    nlinarith only [h4]
  have hD : gaussianSeededTunedConstant false ≤ f.residual := by
    cases f <;>
      norm_num only [gaussianSeededTunedConstant, GaussianTunedProfile.residual, Bool.false_eq_true,
        ite_false]
  have hraw : gaussianSeededTunedRawRoot false L ≤ f.root L :=
    (Analysis.gaussianBudgetRoot_mono (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1
          (add_le_add (le_refl (gaussianMRRefinedConductor * L)) hD)).trans
      (le_max_right _ _)
  have h2 := (sq_le_sq₀ (gaussianSeededTuned_raw_pos false L).le hp.le).mpr hraw
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  rw [seededTuned_eq_max]
  apply max_le
  · exact hf
  · exact mul_le_mul_of_nonneg_left h4 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Below the first triangular entrance and above scale 240, the public tuned selection equals
its two-profile seeded family. Absorb the finite base and every Gaussian candidate. -/
theorem tunedSelected_eq_seeded {n : ℕ} (hN : 3000 ≤ n) (hL : 240 ≤ Real.log n)
    (hU : Real.log n < 30000000000) :
    tunedSelectedEnvelope n = gaussianSeededTunedFamily (Real.log n) := by
  have hn : 1 < n := (by norm_num only : 1 < 3000).trans_le hN
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hG : gaussianSeededTunedFamily (Real.log n) ≤ gaussianTunedFamily (Real.log n) :=
    (min_le_left _ _).trans
      (le_min (seededTuned35_le_gaussian .low hL)
        (le_min (seededTuned35_le_gaussian .bridge hL)
          (le_min (seededTuned35_le_gaussian .middle hL) (seededTuned35_le_gaussian .upper hL))))
  have hF : tunedFiniteSelected n = gaussianSeededSharp (Real.log n) := by
    rw [← tunedFinite_eq_selected hn, tunedFinite_eq_sharp_of_log hn (by linarith only [hL]),
      sharp_eq_selected hn, sharpSelected_eq_seeded hN hL hU]
  rw [tunedSelected_eq_regular hN hU, hF, min_eq_right hG,
    min_eq_right (seededTunedFamily_le_sharp h63)]

/-- On [245,255], the public tuned selection is exactly the raw 35000 seeded curve.
Certified rational switch bounds remove both prefix floors without numerical crossings. -/
theorem tunedSelected_eq_raw35 {n : ℕ} (hN : 3000 ≤ n) (hL : 245 ≤ Real.log n)
    (hU : Real.log n ≤ 255) :
    tunedSelectedEnvelope n = gaussianSeededTunedRawBound false (Real.log n) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h35 : ¬Real.log n ≤ gaussianSeededTunedSwitch false 35000 := by
    dsimp only [gaussianSeededTunedSwitch]
    linarith only [hL, gaussianSeededSharp_switch35_bounds.2, (seededTuned_shift_bounds false).2]
  have h50 : Real.log n < gaussianSeededTunedSwitch false 50000 := by
    dsimp only [gaussianSeededTunedSwitch]
    linarith only [hU, (gaussianSeededSharp_switch50_bounds false).1,
      (seededTuned_shift_bounds false).1]
  rw [tunedSelected_eq_seeded hN (by linarith only [hL]) (by linarith only [hU]),
    seededTunedFamily_eq_selected h63, gaussianSeededTunedSelected, ite_eq_right h35,
    ite_eq_left h50]

/-- From scale 300 to the first high entrance, the tuned selection is its raw 50000 curve.
The three certified switch bounds remove all prefix-floor branches. -/
theorem tunedSelected_eq_raw50 {n : ℕ} (hN : 3000 ≤ n) (hL : 300 ≤ Real.log n)
    (hU : Real.log n < 30000000000) :
    tunedSelectedEnvelope n = gaussianSeededTunedRawBound true (Real.log n) := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h35 : ¬Real.log n ≤ gaussianSeededTunedSwitch false 35000 := by
    dsimp only [gaussianSeededTunedSwitch]
    linarith only [hL, gaussianSeededSharp_switch35_bounds.2, (seededTuned_shift_bounds false).2]
  have h50 (f : Bool) : gaussianSeededTunedSwitch f 50000 < Real.log n := by
    dsimp only [gaussianSeededTunedSwitch]
    linarith only [hL, (gaussianSeededSharp_switch50_bounds f).2, (seededTuned_shift_bounds f).2]
  rw [tunedSelected_eq_seeded hN (by linarith only [hL]) hU, seededTunedFamily_eq_selected h63,
    gaussianSeededTunedSelected, ite_eq_right h35, ite_eq_right (not_lt.mpr (h50 false).le),
    ite_eq_right (not_le.mpr (h50 true))]

end PseudoPrime.PrimeTestBounds.MillerRabin
