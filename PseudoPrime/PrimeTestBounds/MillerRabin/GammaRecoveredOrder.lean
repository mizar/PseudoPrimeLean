/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaRecoveredBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.NextIntervalSelection

/-! # Continuous strict improvements for the recovered Gamma witness cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For L>=101, the reflected Gamma bound is strictly below G1. Its gap
gain at the baseline root is 4071/24700>0, forcing a strictly smaller root
and hence a strictly smaller cutoff. -/
theorem gammaRecovered_lt_reflected {L : ℝ} (hL : 101 ≤ L) :
    gammaRecoveredBound L < gammaReflectedBound L := by
  have h100 : (100 : ℝ) ≤ L := by linarith only [hL]
  let r := gammaReflectedRoot L
  have hr : 0 < r := gammaReflectedRoot_pos h100
  have he : gammaReflectedGap L r = 0 := gammaReflectedGap_root_eq_zero h100
  have hid : gammaRecoveredGap L r - gammaReflectedGap L r = (4071 / 24700 : ℝ) := by
    dsimp only [gammaRecoveredGap, gammaReflectedGap]
    ring
  have hpos : (0 : ℝ) < 4071 / 24700 := by norm_num only
  have hg : 0 < gammaRecoveredGap L r := by linarith only [hid, he, hpos]
  have hle := gammaRecoveredRoot_le_of_gap_nonneg hL hr hg.le
  have hlt : gammaRecoveredRoot L < r := by
    by_contra hn
    have heq := le_antisymm hle (le_of_not_gt hn)
    rw [← heq, gammaRecoveredGap_root_eq_zero hL] at hg
    exact lt_irrefl 0 hg
  have hs := (sq_lt_sq₀ (gammaRecoveredRoot_pos hL).le hr.le).mpr hlt
  exact mul_lt_mul_of_pos_left hs (by norm_num only : (0 : ℝ) < 99 / 40)

/-- A nonnegative reflected gap at a positive affine-radius anchor persists
for larger L when both increment coefficients are nonnegative. Factor
the exact affine and reciprocal increments to certify continuous comparisons. -/
theorem gammaRecoveredGap_affine_nonneg {L L₀ a t : ℝ} (hLL₀ : L₀ ≤ L) (ha : 0 ≤ a)
    (hr₀ : 0 < a * L₀ + t) (hslope : 0 ≤ (86733 / 98800 : ℝ) * a - 11783423 / 25000000)
    (hrecip : 0 ≤ a * (58129633 / 2223000 : ℝ) - (7 / 6 : ℝ) * t)
    (hanchor : 0 ≤ gammaRecoveredGap L₀ (a * L₀ + t)) : 0 ≤ gammaRecoveredGap L (a * L + t) := by
  let r := a * L + t
  let r₀ := a * L₀ + t
  have hdelta : 0 ≤ L - L₀ := by linarith only [hLL₀]
  have hr0 : 0 < r₀ := hr₀
  have hrEq : r = r₀ + a * (L - L₀) := by
    dsimp only [r, r₀]
    ring
  have hr : 0 < r := by
    rw [hrEq]
    exact add_pos_of_pos_of_nonneg hr0 (mul_nonneg ha hdelta)
  have hrExpr : 0 < a * L + t := by simpa only [r] using hr
  have hr0Expr : 0 < a * L₀ + t := by simpa only [r₀] using hr0
  have hid :
    gammaRecoveredGap L r - gammaRecoveredGap L₀ r₀ =
      ((86733 / 98800 : ℝ) * a - 11783423 / 25000000) * (L - L₀) +
        (a * (58129633 / 2223000 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    have hnum :
      ((7 / 6 : ℝ) * L₀ + 58129633 / 2223000) * r - r₀ * ((7 / 6 : ℝ) * L + 58129633 / 2223000) =
        (a * (58129633 / 2223000 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) := by
      dsimp only [r, r₀]
      ring
    calc
      _ =
          ((86733 / 98800 : ℝ) * a - 11783423 / 25000000) * (L - L₀) +
            (((7 / 6 : ℝ) * L₀ + 58129633 / 2223000) / r₀ -
              ((7 / 6 : ℝ) * L + 58129633 / 2223000) / r) :=
        by
        dsimp only [gammaRecoveredGap, r, r₀]
        ring
      _ = _ := by rw [div_sub_div _ _ hr0.ne' hr.ne', hnum, mul_comm r₀ r]
  have hlinear := mul_nonneg hslope hdelta
  have hfrac : 0 ≤ (a * (58129633 / 2223000 : ℝ) - (7 / 6 : ℝ) * t) * (L - L₀) / (r * r₀) := by
    apply div_nonneg
    · exact mul_nonneg hrecip hdelta
    · exact mul_nonneg hr.le hr0.le
  have hstep : 0 ≤ gammaRecoveredGap L r - gammaRecoveredGap L₀ r₀ := by
    rw [hid]
    exact add_nonneg hlinear hfrac
  change 0 ≤ gammaRecoveredGap L r
  have hstep' : 0 ≤ gammaRecoveredGap L r - gammaRecoveredGap L₀ (a * L₀ + t) := by
    simpa only [r₀] using hstep
  linarith only [hanchor, hstep']

/-- For L>=101, an affine reflected-gap certificate bounds G2 strictly
below (L-U) squared. The rational factor eta=15891/25000 has
(99/40) eta squared<1, supplying strictness after the root comparison. -/
theorem gammaRecovered_lt_affine_sq {L L₀ U : ℝ} (hL : 101 ≤ L) (hlo : L₀ ≤ L) (hpos : 0 < L₀ - U)
    (hrecip : 0 ≤ (15891 / 25000 : ℝ) * (58129633 / 2223000) + (7 / 6) * (15891 / 25000) * U)
    (hanchor : 0 ≤ gammaRecoveredGap L₀ ((15891 / 25000) * (L₀ - U))) :
    gammaRecoveredBound L < (L - U) ^ 2 := by
  have hLU : 0 < L - U := by linarith only [hlo, hpos]
  have hr : 0 < (15891 / 25000 : ℝ) * (L - U) := mul_pos (by norm_num only) hLU
  have hg :=
    gammaRecoveredGap_affine_nonneg (a := 15891 / 25000) (t := -(15891 / 25000) * U) hlo
      (by norm_num only) (by nlinarith only [hpos]) (by norm_num only) (by linarith only [hrecip])
      (by
        convert hanchor using 1; congr 1; ring)
  have hroot :=
    gammaRecoveredRoot_le_of_gap_nonneg hL hr
      (by
        convert hg using 1; congr 1; ring)
  have hs := (sq_le_sq₀ (gammaRecoveredRoot_pos hL).le hr.le).mpr hroot
  have hp := sq_pos_of_pos hLU
  change (99 / 40 : ℝ) * gammaRecoveredRoot L ^ 2 < (L - U) ^ 2
  nlinarith only [hs, hp]

/-- The full pointwise correction, including its reciprocal-loss numerator, is
below seven at 539/5. A checked logarithm interval controls the quadratic polynomial. -/
theorem pointwise_correction107_lt :
    LLS.PaperStatements.pointwiseCorrection (539 / 5) < (7 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (539 / 5) 7 16 (117 / 25) (4681 / 1000) = true := by
    decide +kernel
  have hz := Analysis.rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hz
  have hz0 : 0 ≤ Real.log (539 / 5 : ℝ) := by linarith only [hz.1]
  have hsq :=
    mul_nonneg (sub_nonneg.mpr hz.2) (add_nonneg (by norm_num only : (0 : ℝ) ≤ 4681 / 1000) hz0)
  apply
    (div_lt_iff₀
        (mul_pos (by norm_num only : (0 : ℝ) < 18310000)
          (LLS.PaperStatements.fullEndpointEvenGapDenominator_pos
            (by norm_num only : (8 : ℝ) ≤ 539 / 5)))).mpr
  norm_num only [LLS.PaperStatements.pointwiseCorrection,
    LLS.PaperStatements.fullEndpointEvenGapCorrectionNumerator,
    LLS.PaperStatements.fullEndpointEvenGapDenominator, LLS.PaperStatements.pointwiseExtra]
  nlinarith only [hz.1, hz.2, hsq]

/-- The full pointwise correction is below 36/5 at 614/5. The same rational
Taylor checker and positive quadratic envelope retain every extra-numerator term. -/
theorem pointwise_correction122_lt :
    LLS.PaperStatements.pointwiseCorrection (614 / 5) < (36 / 5 : ℝ) := by
  have hc : Analysis.rationalLogIntervalCheck (614 / 5) 7 16 (481 / 100) (4811 / 1000) = true := by
    decide +kernel
  have hz := Analysis.rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hz
  have hz0 : 0 ≤ Real.log (614 / 5 : ℝ) := by linarith only [hz.1]
  have hsq :=
    mul_nonneg (sub_nonneg.mpr hz.2) (add_nonneg (by norm_num only : (0 : ℝ) ≤ 4811 / 1000) hz0)
  apply
    (div_lt_iff₀
        (mul_pos (by norm_num only : (0 : ℝ) < 18310000)
          (LLS.PaperStatements.fullEndpointEvenGapDenominator_pos
            (by norm_num only : (8 : ℝ) ≤ 614 / 5)))).mpr
  norm_num only [LLS.PaperStatements.pointwiseCorrection,
    LLS.PaperStatements.fullEndpointEvenGapCorrectionNumerator,
    LLS.PaperStatements.fullEndpointEvenGapDenominator, LLS.PaperStatements.pointwiseExtra]
  nlinarith only [hz.1, hz.2, hsq]

/-- At L>=108 a correction cap at a radius beyond L-16/5 bounds the inverse
radius below by L-U. Use its exact level equation and monotonicity of the full correction. -/
theorem pointwise_radius_lower_of_cap {L y U : ℝ} (hL : 108 ≤ L) (hy : 8 ≤ y) (hY : L - 16 / 5 ≤ y)
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

/-- For 108<=L<=111, the recovered Gamma cutoff is strictly below the
pointwise cutoff. Bound its radius by eta(L-7) and the inverse pointwise radius below by L-7. -/
theorem gammaRecovered_lt_pointwise111 {L : ℝ} (hL : 108 ≤ L) (hU : L ≤ 111) :
    gammaRecoveredBound L < LLS.PaperStatements.pointwiseCutoff L := by
  have hg :=
    gammaRecovered_lt_affine_sq (L₀ := 108) (U := 7) (by linarith only [hL]) hL (by norm_num only)
      (by norm_num only) (by norm_num only [gammaRecoveredGap])
  have hr :=
    pointwise_radius_lower_of_cap hL (by norm_num only : (8 : ℝ) ≤ 539 / 5) (by linarith only [hU])
      pointwise_correction107_lt.le
  have hs :=
    (sq_le_sq₀ (by linarith only [hL] : (0 : ℝ) ≤ L - 7)
          (by linarith only [(LLS.PaperStatements.pointwiseRadius_spec L).1] :
            (0 : ℝ) ≤ LLS.PaperStatements.pointwiseRadius L)).mpr
      hr
  exact hg.trans_le hs

/-- For 111<=L<=126, use the full correction cap 36/5 at 614/5 to obtain
strict improvement of the recovered Gamma cutoff over the pointwise cutoff. -/
theorem gammaRecovered_lt_pointwise126 {L : ℝ} (hL : 111 ≤ L) (hU : L ≤ 126) :
    gammaRecoveredBound L < LLS.PaperStatements.pointwiseCutoff L := by
  have hg :=
    gammaRecovered_lt_affine_sq (L₀ := 111) (U := 36 / 5) (by linarith only [hL]) hL
      (by norm_num only) (by norm_num only) (by norm_num only [gammaRecoveredGap])
  have hr :=
    pointwise_radius_lower_of_cap (by linarith only [hL]) (by norm_num only : (8 : ℝ) ≤ 614 / 5)
      (by linarith only [hU]) pointwise_correction122_lt.le
  have hs :=
    (sq_le_sq₀ (by linarith only [hL] : (0 : ℝ) ≤ L - 36 / 5)
          (by linarith only [(LLS.PaperStatements.pointwiseRadius_spec L).1] :
            (0 : ℝ) ≤ LLS.PaperStatements.pointwiseRadius L)).mpr
      hr
  exact hg.trans_le hs

/-- On the entire real interval [108,126], the recovered Gamma cutoff strictly
improves the pointwise cutoff. The two rational correction anchors cover the interval. -/
theorem gammaRecovered_lt_pointwise {L : ℝ} (hL : 108 ≤ L) (hU : L ≤ 126) :
    gammaRecoveredBound L < LLS.PaperStatements.pointwiseCutoff L := by
  by_cases h : L ≤ 111
  · exact gammaRecovered_lt_pointwise111 hL h
  · exact gammaRecovered_lt_pointwise126 (le_of_not_ge h) hU

/-- On [108,126] the recovered Gamma root lies below the affine radius
27L/50+6. Its positive gap at 108 persists by the exact affine increment identity. -/
theorem gammaRecovered_affine_upper {L : ℝ} (hL : 108 ≤ L) :
    gammaRecoveredBound L ≤ (99 / 40 : ℝ) * ((27 / 50 : ℝ) * L + 6) ^ 2 := by
  have hg :=
    gammaRecoveredGap_affine_nonneg (L₀ := 108) (a := 27 / 50) (t := 6) hL (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [gammaRecoveredGap])
  have hr : (0 : ℝ) < (27 / 50 : ℝ) * L + 6 := by linarith only [hL]
  have hb := gammaRecoveredRoot_le_of_gap_nonneg (by linarith only [hL]) hr hg
  have hs := (sq_le_sq₀ (gammaRecoveredRoot_pos (by linarith only [hL])).le hr.le).mpr hb
  exact mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 99 / 40)

/-- The old combined Gaussian radius is at least its index-four affine budget
anchor. Its root is at least ten; insert that floor in the exact four-budget inequality. -/
theorem gaussian1000_radius_affine_lower {L : ℝ} (hL : 0 ≤ L) :
    (20115621 / 37554500 : ℝ) * L + 2918336 / 75109 ≤ Analysis.gaussian1000Radius L := by
  have hb := Analysis.gaussian1000_four_budget hL
  have ht := Analysis.gaussian1000_root_ten L
  norm_num only [Analysis.gaussian1000FourD, Analysis.gaussian1000FourBeta,
    Analysis.gaussianMRRefinedConductor, Analysis.gaussianMRRefinedMass,
    Analysis.gaussianMRRefinedWidth, Analysis.gaussianMR6FifthsEndpoint] at hb
  linarith only [hb, ht]

/-- On the real interval [108,126], the recovered Gamma cutoff is strictly
below the old two-root Gaussian cutoff. The rational quadratic difference is positive
throughout the interval, including its smaller value at the right endpoint. -/
theorem gammaRecovered_lt_gaussian1000 {L : ℝ} (hL : 108 ≤ L) (hU : L ≤ 126) :
    gammaRecoveredBound L < Analysis.gaussian1000Bound L := by
  have hnew := gammaRecovered_affine_upper hL
  have hold := gaussian1000_radius_affine_lower (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hpos : (0 : ℝ) ≤ (20115621 / 37554500 : ℝ) * L + 2918336 / 75109 := by linarith only [hL]
  have hs :=
    (sq_le_sq₀ hpos
          (by linarith only [Analysis.gaussian1000_radius_hundred L] :
            (0 : ℝ) ≤ Analysis.gaussian1000Radius L)).mpr
      hold
  have hp := mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hU)
  have hquad :
    (99 / 40 : ℝ) * ((27 / 50 : ℝ) * L + 6) ^ 2 <
      (6 / 5 : ℝ) * ((20115621 / 37554500 : ℝ) * L + 2918336 / 75109) ^ 2 := by
    nlinarith only [hL, hU, hp]
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 6 / 5)
  exact hnew.trans_lt (hquad.trans_le hm)

/-- For every n>1 with 108<=log n<=126, the recovered Gamma cutoff strictly
improves the baseline next-selected envelope. Compare all three surviving baseline candidates
on the continuous real interval before taking their minimum. -/
theorem gammaRecovered_lt_nextSelected {n : ℕ} (hn : 1 < n) (hL : 108 ≤ Real.log n)
    (hU : Real.log n ≤ 126) : gammaRecoveredBound (Real.log n) < nextSelectedEnvelope n := by
  rw [← next_eq_selected hn,
    next_eq_middle_three hn (by linarith only [hL]) (by linarith only [hU])]
  exact
    lt_min (gammaRecovered_lt_pointwise hL hU)
      (lt_min (gammaRecovered_lt_reflected (by linarith only [hL]))
        (gammaRecovered_lt_gaussian1000 hL hU))

/-- For 108<=L<=118 the recovered Gamma cutoff is below 12000. A positive
fixed-radius gap at the right endpoint bounds its root throughout the interval. -/
theorem gammaRecovered_lt_12000 {L : ℝ} (hL : 108 ≤ L) (hU : L ≤ 118) :
    gammaRecoveredBound L < (12000 : ℝ) := by
  have hg : 0 ≤ gammaRecoveredGap L (348 / 5) := by
    dsimp only [gammaRecoveredGap]
    linarith only [hU]
  have hr :=
    gammaRecoveredRoot_le_of_gap_nonneg (by linarith only [hL])
      (by norm_num only : (0 : ℝ) < 348 / 5) hg
  have hs :=
    (sq_le_sq₀ (gammaRecoveredRoot_pos (by linarith only [hL])).le
          (by norm_num only : (0 : ℝ) ≤ 348 / 5)).mpr
      hr
  dsimp only [gammaRecoveredBound]
  nlinarith only [hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
