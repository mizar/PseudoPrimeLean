/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianLowProfiles
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaRecoveredOrder
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedIntervalSelection
public import PseudoPrime.LLS.PaperStatements.EndpointPointwiseNinth

/-! # Continuous low-floor Gaussian comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A strict scalar budget bounds the positive Gaussian root strictly above.
The weak root bound and exact quadratic equation exclude equality. -/
theorem lowGaussian_root_lt {d b C r : ℝ} (hd : 0 < d) (hb : 0 < b) (hC : 0 ≤ C) (hr : b < d * r)
    (hbudget : C + b * r < d * r ^ 2) : Analysis.gaussianBudgetRoot d b C < r := by
  have hle := Analysis.gaussianBudgetRoot_le_of_budget hd hb hC hr hbudget.le
  apply lt_of_le_of_ne hle
  intro heq
  have he := Analysis.gaussianBudgetRoot_equation (b := b) hd hC
  rw [heq] at he
  linarith only [he, hbudget]

/-- A negative quadratic budget at a nonnegative test root places that test
strictly below the positive root. Factor the difference from its exact equation. -/
theorem lowGaussian_root_gt {d b C r : ℝ} (hd : 0 < d) (hb : 0 < b) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hbudget : d * r ^ 2 < b * r + C) : r < Analysis.gaussianBudgetRoot d b C := by
  let t := Analysis.gaussianBudgetRoot d b C
  have ht : 0 < t := Analysis.gaussianBudgetRoot_pos hd hb
  have he : d * t ^ 2 = b * t + C := Analysis.gaussianBudgetRoot_equation hd hC
  have hprod : 0 ≤ t * (d * t - b) := by nlinarith only [he, hC]
  have hlead : 0 ≤ d * t - b := nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hprod) ht
  by_contra hn
  have htr : t ≤ r := le_of_not_gt hn
  have hs : 0 ≤ d * (r + t) - b := by nlinarith only [hlead, mul_nonneg hd.le hr]
  have hp := mul_nonneg (sub_nonneg.mpr htr) hs
  nlinarith only [hp, he, hbudget]

/-- The low profile radius lies below w(L)=13L/20+99/5 for every L>=100.
Completing the quadratic square at L=152 proves the strict budget at sqrt(w).
The rational floor is smaller than sqrt(w), so clipping preserves the bound. -/
theorem gaussianLow_radius_affine {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowRadius (91 / 10) (93 / 10) L < (13 / 20 : ℝ) * L + 99 / 5 := by
  let w := (13 / 20 : ℝ) * L + 99 / 5
  let z := Analysis.gaussianMRRefinedD * w - Analysis.gaussianMRRefinedConductor * L - 93 / 10
  have hw : 0 < w := by
    dsimp only [w]; linarith only [hL]
  have hz : 0 < z := by
    dsimp only [z, w]
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedConductor,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMR6FifthsIndex,
      Analysis.gaussianMR6FifthsEndpoint]
    linarith only [hL]
  have hpoly : Analysis.gaussianMRRefinedBeta ^ 2 * w < z ^ 2 := by
    dsimp only [z, w]
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedConductor,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedWidth, Analysis.gaussianMR6FifthsIndex,
      Analysis.gaussianMR6FifthsEndpoint]
    nlinarith only [sq_nonneg (L - 152), hL]
  have hbudget :
    Analysis.gaussianMRRefinedConductor * L + 93 / 10 +
        Analysis.gaussianMRRefinedBeta * Real.sqrt w <
      Analysis.gaussianMRRefinedD * (Real.sqrt w) ^ 2 := by
    have hs := Real.sq_sqrt hw.le
    have hp := mul_nonneg Analysis.gaussianMRRefined_coefficients.2.le (Real.sqrt_nonneg w)
    dsimp only [z] at hz hpoly
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedConductor,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedWidth, Analysis.gaussianMR6FifthsIndex,
      Analysis.gaussianMR6FifthsEndpoint] at hz hpoly hp ⊢
    nlinarith only [hpoly, hz, hs, hp]
  have hfloor : (91 / 10 : ℝ) < Real.sqrt w := by
    apply (Real.lt_sqrt (by norm_num only)).2
    dsimp only [w]
    linarith only [hL]
  have hcoef : Analysis.gaussianMRRefinedBeta < Analysis.gaussianMRRefinedD * Real.sqrt w := by
    have hm := mul_lt_mul_of_pos_left hfloor Analysis.gaussianMRRefined_coefficients.1
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedMass,
      Analysis.gaussianMRRefinedBeta, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint] at hm ⊢
    linarith only [hm]
  have hC : 0 ≤ Analysis.gaussianMRRefinedConductor * L + 93 / 10 := by
    norm_num only [Analysis.gaussianMRRefinedConductor]
    linarith only [hL]
  have hraw :=
    lowGaussian_root_lt Analysis.gaussianMRRefined_coefficients.1
      Analysis.gaussianMRRefined_coefficients.2 hC hcoef hbudget
  have hr : Analysis.gaussianLowRoot (91 / 10) (93 / 10) L < Real.sqrt w := max_lt hfloor hraw
  have hp : 0 ≤ Analysis.gaussianLowRoot (91 / 10) (93 / 10) L := by
    linarith only [Analysis.gaussianLow_root_floor (91 / 10) (93 / 10) L]
  have hs := (sq_lt_sq₀ hp (Real.sqrt_nonneg w)).mpr hr
  change Analysis.gaussianLowRoot (91 / 10) (93 / 10) L ^ 2 < w
  rw [Real.sq_sqrt hw.le] at hs
  exact hs

/-- At L>=100 the current Gamma root exceeds the affine anchor 107L/200+6.
The quadratic budget at that anchor is negative and decreasing after 100.
This numerical statement does not extend the analytic witness entrance. -/
theorem gammaRecovered_affine_lower100 {L : ℝ} (hL : 100 ≤ L) :
    (107 / 200 : ℝ) * L + 6 < gammaRecoveredRoot L := by
  have hb : 0 < (11783423 / 25000000 : ℝ) * L + 36174637 / 11856000 := by linarith only [hL]
  have hC : 0 ≤ (7 / 6 : ℝ) * L + 58129633 / 2223000 := by linarith only [hL]
  have hr : 0 ≤ (107 / 200 : ℝ) * L + 6 := by linarith only [hL]
  have hbudget :
    (86733 / 98800 : ℝ) * ((107 / 200 : ℝ) * L + 6) ^ 2 <
      ((11783423 / 25000000 : ℝ) * L + 36174637 / 11856000) * ((107 / 200 : ℝ) * L + 6) +
        (7 / 6 : ℝ) * L +
        58129633 / 2223000 := by
    nlinarith only [sq_nonneg (L - 100), hL]
  exact lowGaussian_root_gt (by norm_num only) hb hC hr (by simpa only [add_assoc] using hbudget)

/-- The old reflected Gamma root has the same affine lower bound from its
own entrance L=100. Its larger constant term only decreases the test budget. -/
theorem gammaReflected_affine_lower100 {L : ℝ} (hL : 100 ≤ L) :
    (107 / 200 : ℝ) * L + 6 < gammaReflectedRoot L := by
  have hb : 0 < (11783423 / 25000000 : ℝ) * L + 38128717 / 11856000 := by linarith only [hL]
  have hC : 0 ≤ (7 / 6 : ℝ) * L + 58129633 / 2223000 := by linarith only [hL]
  have hr : 0 ≤ (107 / 200 : ℝ) * L + 6 := by linarith only [hL]
  have hbudget :
    (86733 / 98800 : ℝ) * ((107 / 200 : ℝ) * L + 6) ^ 2 <
      ((11783423 / 25000000 : ℝ) * L + 38128717 / 11856000) * ((107 / 200 : ℝ) * L + 6) +
        (7 / 6 : ℝ) * L +
        58129633 / 2223000 := by
    nlinarith only [sq_nonneg (L - 100), hL]
  exact lowGaussian_root_gt (by norm_num only) hb hC hr (by simpa only [add_assoc] using hbudget)

/-- The low-profile cutoff is bounded by six fifths of the squared affine
radius. Positivity of the radius permits the strict square comparison. -/
theorem gaussianLow_bound_affine {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowBound (91 / 10) (93 / 10) L <
      (6 / 5 : ℝ) * ((13 / 20 : ℝ) * L + 99 / 5) ^ 2 := by
  have hr := gaussianLow_radius_affine hL
  have hp : 0 ≤ Analysis.gaussianLowRadius (91 / 10) (93 / 10) L := sq_nonneg _
  have hs := (sq_lt_sq₀ hp (by linarith only [hL])).mpr hr
  exact mul_lt_mul_of_pos_left hs (by norm_num only)

/-- The Gaussian affine upper cutoff is strictly below the Gamma affine
lower cutoff from L=100 onwards; a positive quadratic in L-100 certifies the gap. -/
theorem gaussianLow_gamma_affine_gap {L : ℝ} (hL : 100 ≤ L) :
    (6 / 5 : ℝ) * ((13 / 20 : ℝ) * L + 99 / 5) ^ 2 <
      (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 6) ^ 2 := by
  nlinarith only [sq_nonneg (L - 100), hL]

/-- The low-profile cutoff strictly dominates the numerical current Gamma
cutoff on the half-line L>=100. Its witness API still keeps entrance 101. -/
theorem gaussianLow_lt_gamma {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowBound (91 / 10) (93 / 10) L < gammaRecoveredBound L := by
  have hr := gammaRecovered_affine_lower100 hL
  have hv : 0 ≤ (107 / 200 : ℝ) * L + 6 := by linarith only [hL]
  have hs := (sq_lt_sq₀ hv (hv.trans hr.le)).mpr hr
  have hc := mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 99 / 40)
  exact ((gaussianLow_bound_affine hL).trans (gaussianLow_gamma_affine_gap hL)).trans hc

/-- The same affine comparison strictly dominates the old reflected Gamma
cutoff from its certified entrance L=100. -/
theorem gaussianLow_lt_reflected {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowBound (91 / 10) (93 / 10) L < gammaReflectedBound L := by
  have hr := gammaReflected_affine_lower100 hL
  have hv : 0 ≤ (107 / 200 : ℝ) * L + 6 := by linarith only [hL]
  have hs := (sq_lt_sq₀ hv (hv.trans hr.le)).mpr hr
  have hc := mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 99 / 40)
  exact ((gaussianLow_bound_affine hL).trans (gaussianLow_gamma_affine_gap hL)).trans hc

/-- At L>=100 a correction cap at a radius beyond L-16/5 bounds the inverse
radius below by L-U. This is the full-correction argument with its numerical
entrance 100; no analytic witness theorem is extended. -/
theorem pointwise_radius_lower100 {L y U : ℝ} (hL : 100 ≤ L) (hy : 8 ≤ y) (hY : L - 16 / 5 ≤ y)
    (hcap : LLS.PaperStatements.pointwiseCorrection y ≤ U) :
    L - U ≤ LLS.PaperStatements.pointwiseRadius L := by
  have hs := LLS.PaperStatements.pointwiseRadius_spec L
  have he : LLS.PaperStatements.pointwiseLevel (LLS.PaperStatements.pointwiseRadius L) = L := by
    rcases hs.2.2 with h8 | hsol
    · rw [h8] at hs
      have hb := LLS.PaperStatements.pointwiseCorrection_eight_lt
      dsimp only [LLS.PaperStatements.pointwiseLevel] at hs
      linarith only [hs.2.1, hb, hL]
    · exact hsol
  have hcorr :
    (16 / 5 : ℝ) <
      LLS.PaperStatements.pointwiseCorrection (LLS.PaperStatements.pointwiseRadius L) := by
    rw [LLS.PaperStatements.pointwiseCorrection_eq hs.1]
    have ha := LLS.PaperStatements.fullEndpointEvenGapCorrection_gt_16over5 hs.1
    have hb := LLS.PaperStatements.pointwiseDelta_pos hs.1
    linarith only [ha, hb]
  have hrad : LLS.PaperStatements.pointwiseRadius L ≤ y := by
    dsimp only [LLS.PaperStatements.pointwiseLevel] at he
    linarith only [he, hcorr, hY]
  have hm := LLS.PaperStatements.pointwiseCorrection_strictMonoOn.monotoneOn hs.1 hy hrad
  dsimp only [LLS.PaperStatements.pointwiseLevel] at he
  linarith only [he, hm, hcap]

/-- The low-profile cutoff lies strictly below the actual pointwise cutoff
throughout L>=100. Two full correction caps cover [100,126], and the
81-percent quadratic lower bound covers the remaining half-line. -/
theorem gaussianLow_lt_pointwise {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowBound (91 / 10) (93 / 10) L < LLS.PaperStatements.pointwiseCutoff L := by
  have ha := gaussianLow_bound_affine hL
  by_cases h111 : L ≤ 111
  · have hr :=
      pointwise_radius_lower100 hL (by norm_num only : (8 : ℝ) ≤ 539 / 5) (by linarith only [h111])
        pointwise_correction107_lt.le
    have hs :=
      (sq_le_sq₀ (by linarith only [hL] : (0 : ℝ) ≤ L - 7)
            (by linarith only [(LLS.PaperStatements.pointwiseRadius_spec L).1] :
              (0 : ℝ) ≤ LLS.PaperStatements.pointwiseRadius L)).mpr
        hr
    have hg : (6 / 5 : ℝ) * ((13 / 20 : ℝ) * L + 99 / 5) ^ 2 < (L - 7) ^ 2 := by
      nlinarith only [sq_nonneg (L - 100), hL]
    exact ha.trans (hg.trans_le hs)
  · by_cases h126 : L ≤ 126
    · have h111' : 111 ≤ L := (lt_of_not_ge h111).le
      have hr :=
        pointwise_radius_lower100 hL (by norm_num only : (8 : ℝ) ≤ 614 / 5)
          (by linarith only [h126]) pointwise_correction122_lt.le
      have hs :=
        (sq_le_sq₀ (by linarith only [hL] : (0 : ℝ) ≤ L - 36 / 5)
              (by linarith only [(LLS.PaperStatements.pointwiseRadius_spec L).1] :
                (0 : ℝ) ≤ LLS.PaperStatements.pointwiseRadius L)).mpr
          hr
      have hg : (6 / 5 : ℝ) * ((13 / 20 : ℝ) * L + 99 / 5) ^ 2 < (L - 36 / 5) ^ 2 := by
        nlinarith only [sq_nonneg (L - 111), h111']
      exact ha.trans (hg.trans_le hs)
    · have h126' : 126 ≤ L := (lt_of_not_ge h126).le
      have hg : (6 / 5 : ℝ) * ((13 / 20 : ℝ) * L + 99 / 5) ^ 2 < (81 / 100 : ℝ) * L ^ 2 := by
        nlinarith only [sq_nonneg (L - 126), h126']
      exact ha.trans (hg.trans_le (LLS.PaperStatements.pointwiseCutoff_lower81 hL))

/-- The old-prefix family is at most its low-profile component. -/
theorem gaussianLowOldFamily_le_low (L : ℝ) :
    Analysis.gaussianLowOldFamily L ≤ Analysis.gaussianLowBound (91 / 10) (93 / 10) L :=
  min_le_left _ _

/-- The fine-prefix family is at most its low-profile component. -/
theorem gaussianLowFamily_le_low (L : ℝ) :
    Analysis.gaussianLowFamily L ≤ Analysis.gaussianLowBound (91 / 10) (93 / 10) L :=
  min_le_left _ _

/-- The fine-prefix family strictly dominates current Gamma on the half-line
L>=100. This comparison also supports the selected-envelope monotonicity proof. -/
theorem gaussianLowFamily_lt_gamma {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowFamily L < gammaRecoveredBound L :=
  (gaussianLowFamily_le_low L).trans_lt (gaussianLow_lt_gamma hL)

/-- The fine-prefix family strictly dominates old reflected Gamma throughout
its certified half-line L>=100. -/
theorem gaussianLowFamily_lt_reflected {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowFamily L < gammaReflectedBound L :=
  (gaussianLowFamily_le_low L).trans_lt (gaussianLow_lt_reflected hL)

/-- The fine-prefix family strictly dominates the actual pointwise cutoff
throughout L>=100, using the low component and the full-correction comparison. -/
theorem gaussianLowFamily_lt_pointwise {L : ℝ} (hL : 100 ≤ L) :
    Analysis.gaussianLowFamily L < LLS.PaperStatements.pointwiseCutoff L :=
  (gaussianLowFamily_le_low L).trans_lt (gaussianLow_lt_pointwise hL)

/-- The old middle profile has root below ten through L=126. Its floor is
9.5 and the raw quadratic budget is strictly positive at ten and L=126. -/
theorem gaussianLowMiddleOld_lt12000 {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 126) :
    Analysis.GaussianLowProfile.middleOld.bound L < (12000 : ℝ) := by
  have hC : 0 ≤ Analysis.gaussianMRRefinedConductor * L + 204 / 25 := by
    norm_num only [Analysis.gaussianMRRefinedConductor]
    linarith only [hL]
  have hcoef : Analysis.gaussianMRRefinedBeta < Analysis.gaussianMRRefinedD * 10 := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedMass,
      Analysis.gaussianMRRefinedBeta, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint]
  have hbudget :
    Analysis.gaussianMRRefinedConductor * L + 204 / 25 + Analysis.gaussianMRRefinedBeta * 10 <
      Analysis.gaussianMRRefinedD * (10 : ℝ) ^ 2 := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedConductor,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedWidth, Analysis.gaussianMR6FifthsIndex,
      Analysis.gaussianMR6FifthsEndpoint]
    linarith only [hU]
  have hraw :=
    lowGaussian_root_lt Analysis.gaussianMRRefined_coefficients.1
      Analysis.gaussianMRRefined_coefficients.2 hC hcoef hbudget
  have hroot : Analysis.GaussianLowProfile.middleOld.root L < (10 : ℝ) :=
    max_lt (by norm_num only [Analysis.GaussianLowProfile.floor]) hraw
  have hp := Analysis.GaussianLowProfile.root_pos .middleOld L
  have hs := (sq_lt_sq₀ hp.le (by norm_num only : (0 : ℝ) ≤ 10)).mpr hroot
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ 10 ^ 2)).mpr hs
  change (6 / 5 : ℝ) * (Analysis.GaussianLowProfile.middleOld.root L ^ 2) ^ 2 < 12000
  nlinarith only [hs']

/-- Through L=126 the old-prefix family lies below the current 12000 floor.
The affine low bound covers the first segment; the old middle certificate
covers the remaining segment through the full endpoint. -/
theorem gaussianLowOldFamily_lt12000 {L : ℝ} (hL : 100 ≤ L) (hU : L ≤ 126) :
    Analysis.gaussianLowOldFamily L < (12000 : ℝ) := by
  by_cases h123 : L ≤ 123
  · have ha := gaussianLow_bound_affine hL
    have hw : 0 ≤ (13 / 20 : ℝ) * L + 99 / 5 := by linarith only [hL]
    have hc : (6 / 5 : ℝ) * ((13 / 20 : ℝ) * L + 99 / 5) ^ 2 < 12000 := by nlinarith only [h123, hL]
    exact (gaussianLowOldFamily_le_low L).trans_lt (ha.trans hc)
  · have hm : Analysis.gaussianLowOldFamily L ≤ Analysis.GaussianLowProfile.middleOld.bound L :=
      (min_le_right _ _).trans (min_le_left _ _)
    exact hm.trans_lt (gaussianLowMiddleOld_lt12000 (by linarith only [hL]) hU)

/-- The fine upper profile strictly improves the current recovered Gaussian
at every nonnegative scale: both its floor and its raw residual are smaller. -/
theorem gaussianLowUpper_lt_recovered {L : ℝ} (hL : 0 ≤ L) :
    Analysis.GaussianLowProfile.upper.bound L < Analysis.gaussianRecoveredBound L := by
  have hC : 0 ≤ Analysis.gaussianMRRefinedConductor * L + 813 / 100 := by
    norm_num only [Analysis.gaussianMRRefinedConductor]
    linarith only [hL]
  have hraw :=
    Analysis.gaussianBudgetRoot_strictMono (b := Analysis.gaussianMRRefinedBeta)
      Analysis.gaussianMRRefined_coefficients.1 hC
      (show
        Analysis.gaussianMRRefinedConductor * L + 813 / 100 <
          Analysis.gaussianMRRefinedConductor * L + 407 / 50
        by linarith only [])
  have hfloor : (49 / 5 : ℝ) < Analysis.gaussianRecoveredRoot L := by
    linarith only [Analysis.gaussianRecovered_root_ten L]
  have hraw' :
    Analysis.gaussianBudgetRoot Analysis.gaussianMRRefinedD Analysis.gaussianMRRefinedBeta
        (Analysis.gaussianMRRefinedConductor * L + 813 / 100) <
      Analysis.gaussianRecoveredRoot L :=
    hraw.trans_le (le_max_right _ _)
  have hr : Analysis.GaussianLowProfile.upper.root L < Analysis.gaussianRecoveredRoot L :=
    max_lt hfloor hraw'
  have hs :=
    (sq_lt_sq₀ (Analysis.GaussianLowProfile.root_pos .upper L).le
          (Analysis.gaussianRecovered_root_pos L).le).mpr
      hr
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
  exact mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5)

/-- Through L=235 the fine upper profile remains below 35000. A rational
root test at 653/50 controls its raw root and its smaller floor. -/
theorem gaussianLowUpper_lt35000 {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 235) :
    Analysis.GaussianLowProfile.upper.bound L < (35000 : ℝ) := by
  have hC : 0 ≤ Analysis.gaussianMRRefinedConductor * L + 813 / 100 := by
    norm_num only [Analysis.gaussianMRRefinedConductor]
    linarith only [hL]
  have hcoef : Analysis.gaussianMRRefinedBeta < Analysis.gaussianMRRefinedD * (653 / 50) := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedMass,
      Analysis.gaussianMRRefinedBeta, Analysis.gaussianMRRefinedWidth,
      Analysis.gaussianMR6FifthsIndex, Analysis.gaussianMR6FifthsEndpoint]
  have hbudget :
    Analysis.gaussianMRRefinedConductor * L + 813 / 100 +
        Analysis.gaussianMRRefinedBeta * (653 / 50) <
      Analysis.gaussianMRRefinedD * (653 / 50 : ℝ) ^ 2 := by
    norm_num only [Analysis.gaussianMRRefinedD, Analysis.gaussianMRRefinedConductor,
      Analysis.gaussianMRRefinedMass, Analysis.gaussianMRRefinedBeta,
      Analysis.gaussianMRRefinedWidth, Analysis.gaussianMR6FifthsIndex,
      Analysis.gaussianMR6FifthsEndpoint]
    linarith only [hU]
  have hraw :=
    lowGaussian_root_lt Analysis.gaussianMRRefined_coefficients.1
      Analysis.gaussianMRRefined_coefficients.2 hC hcoef hbudget
  have hroot : Analysis.GaussianLowProfile.upper.root L < (653 / 50 : ℝ) :=
    max_lt (by norm_num only [Analysis.GaussianLowProfile.floor]) hraw
  have hp := Analysis.GaussianLowProfile.root_pos .upper L
  have hs := (sq_lt_sq₀ hp.le (by norm_num only : (0 : ℝ) ≤ 653 / 50)).mpr hroot
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (by norm_num only : (0 : ℝ) ≤ (653 / 50) ^ 2)).mpr hs
  change (6 / 5 : ℝ) * (Analysis.GaussianLowProfile.upper.root L ^ 2) ^ 2 < 35000
  nlinarith only [hs']

/-- The fine family strictly improves the current recovered Gaussian for
every nonnegative scale, by projecting to its upper component. -/
theorem gaussianLowFamily_lt_recovered {L : ℝ} (hL : 0 ≤ L) :
    Analysis.gaussianLowFamily L < Analysis.gaussianRecoveredBound L :=
  ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (gaussianLowUpper_lt_recovered hL)

/-- Through scale 235 the fine family is below the current seeded floor. -/
theorem gaussianLowFamily_lt35000 {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 235) :
    Analysis.gaussianLowFamily L < (35000 : ℝ) :=
  ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (gaussianLowUpper_lt35000 hL hU)

/-- Every current recovered seeded candidate retains a prefix floor at least
35000. Resolve the minimum into its two clipped profiles and use their floors. -/
theorem currentSeeded_floor35000 {L : ℝ} (hL : 63 ≤ L) :
    (35000 : ℝ) ≤ Analysis.gaussianRecoveredSeeded L := by
  rw [Analysis.gaussianRecoveredSeeded_eq_min hL]
  apply le_min
  · rw [Analysis.gaussianRecoveredSeeded_eq_max]
    exact le_max_left _ _
  · rw [Analysis.gaussianRecoveredSeeded_eq_max]
    exact (by norm_num only : (35000 : ℝ) ≤ 50000).trans (le_max_left _ _)

/-- On [100,235], a cutoff strictly below every valid current analytic
candidate is strictly below the current refined selection. Resolve the
baseline's 132 split and the recovered Gamma entrance 101 explicitly. -/
theorem gaussianFamily_lt_refined {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 235) {A : ℝ} (hP : A < LLS.PaperStatements.pointwiseCutoff (Real.log n))
    (hRef : A < gammaReflectedBound (Real.log n))
    (hG : A < Analysis.gaussianRecoveredBound (Real.log n))
    (hR : A < gammaRecoveredBound (Real.log n)) (hS : A < 35000) :
    A < refinedSelectedEnvelope n := by
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have h1000 := hG.trans_le (Analysis.gaussianRecovered_bound_le (Real.log n))
  have hbase : A < lowPrimeTightSelected n := by
    rw [← lowPrimeTight_eq_selected hn, lowPrimeTight_eq_next_of_log (by linarith only [hL])]
    by_cases h132 : Real.log n < 132
    · rw [next_eq_middle_three hn hL h132]
      exact lt_min hP (lt_min hRef h1000)
    · rw [next_eq_middle_two hn (le_of_not_gt h132) hU]
      exact lt_min hP h1000
  have hseed := hS.trans_le (currentSeeded_floor35000 h63)
  by_cases h101 : Real.log n < 101
  · rw [refinedSelected_eq_before101 h63 h101]
    exact lt_min hbase (lt_min hG hseed)
  · rw [refinedSelected_eq_analytic (le_of_not_gt h101) (by linarith only [hU])]
    exact lt_min hbase (lt_min hG (lt_min hR hseed))

/-- With only the old prefix, the three-profile Gaussian family strictly
improves the current refined selection on the whole closed interval [100,126].
All active baseline and analytic candidates are compared explicitly. -/
theorem gaussianLowOldFamily_lt_refined {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 126) :
    Analysis.gaussianLowOldFamily (Real.log n) < refinedSelectedEnvelope n := by
  have hfloor := gaussianLowOldFamily_lt12000 hL hU
  apply gaussianFamily_lt_refined hn hL (by linarith only [hU])
  · exact (gaussianLowOldFamily_le_low _).trans_lt (gaussianLow_lt_pointwise hL)
  · exact (gaussianLowOldFamily_le_low _).trans_lt (gaussianLow_lt_reflected hL)
  · exact hfloor.trans_le (Analysis.gaussianRecovered_cutoff_floor _)
  · exact (gaussianLowOldFamily_le_low _).trans_lt (gaussianLow_lt_gamma hL)
  · linarith only [hfloor]

/-- After the fine-prefix certificates, the Gaussian family strictly improves
the current refined selection throughout [100,235]. Its upper component is
strictly below recovered Gaussian and remains below the seeded floor 35000. -/
theorem gaussianLowFamily_lt_refined {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n ≤ 235) :
    Analysis.gaussianLowFamily (Real.log n) < refinedSelectedEnvelope n := by
  have h0 : (0 : ℝ) ≤ Real.log n := by linarith only [hL]
  exact
    gaussianFamily_lt_refined hn hL hU (gaussianLowFamily_lt_pointwise hL)
      (gaussianLowFamily_lt_reflected hL) (gaussianLowFamily_lt_recovered h0)
      (gaussianLowFamily_lt_gamma hL) (gaussianLowFamily_lt35000 h0 hU)

/-- Every profile retains the square of the 9.1 floor, so the family is at
least (6/5)(9.1)^4 at every real scale. This removes inactive numerical guards. -/
theorem gaussianLowFamily_floor (L : ℝ) :
    (6 / 5 : ℝ) * (91 / 10 : ℝ) ^ 4 ≤ Analysis.gaussianLowFamily L := by
  apply le_min
  · have h := Analysis.GaussianLowProfile.radius_floor .low L
    change _ ≤ (6 / 5 : ℝ) * Analysis.GaussianLowProfile.low.radius L ^ 2
    nlinarith only [h]
  · apply le_min
    · have h := Analysis.GaussianLowProfile.radius_floor .middle L
      change _ ≤ (6 / 5 : ℝ) * Analysis.GaussianLowProfile.middle.radius L ^ 2
      nlinarith only [h]
    · have h := Analysis.GaussianLowProfile.radius_floor .upper L
      change _ ≤ (6 / 5 : ℝ) * Analysis.GaussianLowProfile.upper.radius L ^ 2
      nlinarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
