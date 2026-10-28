/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointCorrectionIntervals
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointMidscaleEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaRefinedEnvelope

/-! # Continuous envelope comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For L>=23/2, any strict upper bound on the positive second radius gives a strict
square bound on the cutoff. Positivity follows from the first-radius floor eight. -/
theorem twoStep_lt_sq {L r : ℝ} (hL : 23 / 2 ≤ L)
    (hr : LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L < r) :
    LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L < r ^ 2 := by
  have hb := LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius_gt_first hL
  have ha : (8 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have hpos : 0 ≤ LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L := by
    linarith only [ha, hb]
  exact (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr

/-- On 23/2<=L<=122, the two-step cutoff strictly dominates every endpoint-base branch.
Apply continuous rational comparison bands and square their positive radius bounds.
This removes the endpoint candidates from the public midscale envelope. -/
theorem twoStep_lt_endpoint {L : ℝ} (hL : 23 / 2 ≤ L) (hU : L ≤ 122) :
    LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L < endpointMidscaleBase L := by
  by_cases h8 : L ≤ 22
  · rw [endpointMidscaleBase, ite_eq_left h8]
    by_cases h14 : L ≤ 74 / 5
    · exact LLS.PaperStatements.fullEndpointEvenTwoStepCutoff_lt_shifted_sevenFourths hL h14
    · have h :=
        twoStep_lt_sq hL
          (LLS.PaperStatements.endpointOrderBand0_sound (L := L) (le_of_not_ge h14) h8)
      nlinarith only [h]
  · by_cases h9 : L ≤ 111 / 4
    · rw [endpointMidscaleBase, ite_eq_right h8, ite_eq_left h9]
      have h :=
        twoStep_lt_sq hL
          (LLS.PaperStatements.endpointOrderBand1_sound (L := L) (le_of_not_ge h8) h9)
      nlinarith only [h]
    · by_cases hf : L ≤ 144 / 5
      · rw [endpointMidscaleBase, ite_eq_right h8, ite_eq_right h9, ite_eq_left hf]
        have h :=
          twoStep_lt_sq hL
            (LLS.PaperStatements.endpointOrderBand2_sound (L := L) (le_of_not_ge h9) hf)
        norm_num only [zero_mul, zero_add, Nat.reducePow] at h
        exact h
      · rw [endpointMidscaleBase, ite_eq_right h8, ite_eq_right h9, ite_eq_right hf]
        by_cases h1 : L - 7 / 4 ≤ 703 / 20
        · rw [LLS.PaperStatements.midscaleEndpointRadius, ite_eq_left h1]
          have hb :=
            LLS.PaperStatements.endpointOrderBand3_sound (L := L) (le_of_not_ge hf)
              (by linarith only [h1])
          apply twoStep_lt_sq hL
          linarith only [hb]
        · by_cases h2 : L - 7 / 4 ≤ 10367 / 200
          · rw [LLS.PaperStatements.midscaleEndpointRadius, ite_eq_right h1, ite_eq_left h2]
            have hb :=
              LLS.PaperStatements.endpointOrderBand4_sound (L := L) (by linarith only [h1])
                (by linarith only [h2])
            apply twoStep_lt_sq hL
            linarith only [hb]
          · by_cases h3 : L - 7 / 4 ≤ 1706 / 25
            · rw [LLS.PaperStatements.midscaleEndpointRadius, ite_eq_right h1, ite_eq_right h2,
                ite_eq_left h3]
              have hb :=
                LLS.PaperStatements.endpointOrderBand5_sound (L := L) (by linarith only [h2])
                  (by linarith only [h3])
              apply twoStep_lt_sq hL
              linarith only [hb]
            · have h4 : L - 7 / 4 ≤ 6671 / 50 := by linarith only [hU]
              rw [LLS.PaperStatements.midscaleEndpointRadius, ite_eq_right h1, ite_eq_right h2,
                ite_eq_right h3, ite_eq_left h4]
              have hb :=
                LLS.PaperStatements.endpointOrderBand6_sound (L := L) (by linarith only [h3]) hU
              apply twoStep_lt_sq hL
              linarith only [hb]

/-- An upper correction bound at q bounds the correction at the first radius whenever
that radius is at most q. Monotonicity then gives a lower bound on the second radius. -/
theorem correction_upper_of_cap {L q U : ℝ} (hq : 8 ≤ q)
    (hfirst : LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L ≤ q)
    (hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection q ≤ U) :
    L - U ≤ LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L := by
  have ha : (8 : ℝ) ≤ LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have h := LLS.PaperStatements.fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn ha hq hfirst
  dsimp only [LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius]
  linarith only [h, hcap]

/-- An affine Gamma gap certificate and a lower second-radius bound imply strict
dominance of the refined Gamma bound. The rational slope has scaled square below one;
root comparison and the prefix floor control the whole clipped radius. -/
theorem gamma_lt_twoStep_of_cap {L L₀ U : ℝ} (hL : 120 ≤ L) (hlo : L₀ ≤ L)
    (hr0 : 0 < (15891 / 25000 : ℝ) * (L₀ - U))
    (hfloor : (40 / 99 : ℝ) * 1000 ≤ ((15891 / 25000 : ℝ) * (L₀ - U)) ^ 2)
    (hrecip : 0 ≤ (15891 / 25000 : ℝ) * (190 / 3) + (7 / 6) * (15891 / 25000) * U)
    (hgap : 0 ≤ gammaClippedPrefixGap L₀ (413 / 100) ((15891 / 25000) * (L₀ - U)))
    (hB : L - U ≤ LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L) :
    gamma1000RefinedBound L < LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L := by
  let c : ℝ := 15891 / 25000
  have hc : 0 < c := by norm_num only [c]
  have hr : 0 < c * (L - U) := by nlinarith only [hr0, hlo, hc]
  have hg :=
    gammaClippedPrefixGap_affine_nonneg (C := 413 / 100) (t := -c * U) hlo hc.le
      (by
        dsimp only [c]; linarith only [hr0])
      (by norm_num only [c])
      (by
        dsimp only [c]; linarith only [hrecip])
      (by
        convert hgap using 1
        dsimp only [c]
        congr 1
        ring)
  have hroot : gammaClippedPrefixRoot L (413 / 100) ≤ c * (L - U) := by
    apply gammaClippedPrefixRoot_le_of_gap_nonneg hL (by norm_num only) hr
    convert hg using 1
    congr 1
    ring
  have hf : Real.sqrt ((40 / 99 : ℝ) * 1000) ≤ c * (L - U) := by
    apply Real.sqrt_le_iff.mpr ⟨hr.le, ?_⟩
    have hstep : c * (L₀ - U) ≤ c * (L - U) := by nlinarith only [hlo, hc]
    exact hfloor.trans ((sq_le_sq₀ hr0.le hr.le).mpr hstep)
  have hradius : gammaClippedPrefixRadius L 1000 (413 / 100) ≤ c * (L - U) := max_le hf hroot
  have hpos : 0 ≤ gammaClippedPrefixRadius L 1000 (413 / 100) :=
    (Real.sqrt_nonneg _).trans (le_max_left _ _)
  have hs := (sq_le_sq₀ hpos hr.le).mpr hradius
  have hLU : 0 < L - U := by nlinarith only [hr, hc]
  have hBsq := (sq_le_sq₀ hLU.le (hLU.le.trans hB)).mpr hB
  change
    (99 / 40 : ℝ) * gammaClippedPrefixRadius L 1000 (413 / 100) ^ 2 <
      LLS.PaperStatements.fullEndpointEvenCorrectionSecondRadius L ^ 2
  have hstrict : (99 / 40 : ℝ) * c ^ 2 < 1 := by norm_num only [c]
  have hm := mul_lt_mul_of_pos_right hstrict (sq_pos_of_pos hLU)
  nlinarith only [hs, hBsq, hm]

/-- On continuous band 0, the refined Gamma bound is below the two-step cutoff.
A kernel-checked correction cap yields a lower radius bound; the affine gap
certificate controls the Gamma root throughout the band. -/
theorem gamma_twoStep_band0 {L : ℝ} (hlo : (120 : ℝ) ≤ L) (hhi : L ≤ (602 / 5 : ℝ)) :
    gamma1000RefinedBound L < LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L := by
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck (586 / 5) 0 (3559 / 500) = true := by
    decide +kernel
  have hcap := (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).2
  have hcapR :
    LLS.PaperStatements.fullEndpointEvenGapCorrection (586 / 5 : ℝ) ≤ (3559 / 500 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcap
  have hfirst : LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L ≤ (586 / 5 : ℝ) := by
    apply max_le (by norm_num only)
    have hcor :=
      LLS.PaperStatements.fullEndpointEvenGapCorrection_gt_16over5
        (by linarith only [hlo] : (8 : ℝ) ≤ L)
    linarith only [hhi, hcor]
  have hB := correction_upper_of_cap (by norm_num only : (8 : ℝ) ≤ 586 / 5) hfirst hcapR
  apply gamma_lt_twoStep_of_cap (L₀ := 120) (U := 3559 / 500) (by linarith only [hlo]) hlo
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only [gammaClippedPrefixGap]
  · exact hB

/-- On continuous band 1, the refined Gamma bound is below the two-step cutoff.
A kernel-checked correction cap yields a lower radius bound; the affine gap
certificate controls the Gamma root throughout the band. -/
theorem gamma_twoStep_band1 {L : ℝ} (hlo : (602 / 5 : ℝ) ≤ L) (hhi : L ≤ (122 : ℝ)) :
    gamma1000RefinedBound L < LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L := by
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck (594 / 5) 0 (357 / 50) = true := by
    decide +kernel
  have hcap := (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).2
  have hcapR :
    LLS.PaperStatements.fullEndpointEvenGapCorrection (594 / 5 : ℝ) ≤ (357 / 50 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcap
  have hfirst : LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L ≤ (594 / 5 : ℝ) := by
    apply max_le (by norm_num only)
    have hcor :=
      LLS.PaperStatements.fullEndpointEvenGapCorrection_gt_16over5
        (by linarith only [hlo] : (8 : ℝ) ≤ L)
    linarith only [hhi, hcor]
  have hB := correction_upper_of_cap (by norm_num only : (8 : ℝ) ≤ 594 / 5) hfirst hcapR
  apply gamma_lt_twoStep_of_cap (L₀ := 602 / 5) (U := 357 / 50) (by linarith only [hlo]) hlo
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only [gammaClippedPrefixGap]
  · exact hB

/-- On continuous band 2, the refined Gamma bound is below the two-step cutoff.
A kernel-checked correction cap yields a lower radius bound; the affine gap
certificate controls the Gamma root throughout the band. -/
theorem gamma_twoStep_band2 {L : ℝ} (hlo : (122 : ℝ) ≤ L) (hhi : L ≤ (140 : ℝ)) :
    gamma1000RefinedBound L < LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L := by
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck (140) 0 (37 / 5) = true := by
    decide +kernel
  have hcap := (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).2
  have hcapR : LLS.PaperStatements.fullEndpointEvenGapCorrection (140 : ℝ) ≤ (37 / 5 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcap
  have hfirst : LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L ≤ (140 : ℝ) := by
    apply max_le (by norm_num only)
    have hcor :=
      LLS.PaperStatements.fullEndpointEvenGapCorrection_gt_16over5
        (by linarith only [hlo] : (8 : ℝ) ≤ L)
    linarith only [hhi, hcor]
  have hB := correction_upper_of_cap (by norm_num only : (8 : ℝ) ≤ 140) hfirst hcapR
  apply gamma_lt_twoStep_of_cap (L₀ := 122) (U := 37 / 5) (by linarith only [hlo]) hlo
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only [gammaClippedPrefixGap]
  · exact hB

/-- On continuous band 3, the refined Gamma bound is below the two-step cutoff.
A kernel-checked correction cap yields a lower radius bound; the affine gap
certificate controls the Gamma root throughout the band. -/
theorem gamma_twoStep_band3 {L : ℝ} (hlo : (140 : ℝ) ≤ L) (hhi : L ≤ (180 : ℝ)) :
    gamma1000RefinedBound L < LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L := by
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck (180) 0 (8) = true := by decide +kernel
  have hcap := (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).2
  have hcapR : LLS.PaperStatements.fullEndpointEvenGapCorrection (180 : ℝ) ≤ (8 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcap
  have hfirst : LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L ≤ (180 : ℝ) := by
    apply max_le (by norm_num only)
    have hcor :=
      LLS.PaperStatements.fullEndpointEvenGapCorrection_gt_16over5
        (by linarith only [hlo] : (8 : ℝ) ≤ L)
    linarith only [hhi, hcor]
  have hB := correction_upper_of_cap (by norm_num only : (8 : ℝ) ≤ 180) hfirst hcapR
  apply gamma_lt_twoStep_of_cap (L₀ := 140) (U := 8) (by linarith only [hlo]) hlo
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only [gammaClippedPrefixGap]
  · exact hB

/-- On continuous band 4, the refined Gamma bound is below the two-step cutoff.
A kernel-checked correction cap yields a lower radius bound; the affine gap
certificate controls the Gamma root throughout the band. -/
theorem gamma_twoStep_band4 {L : ℝ} (hlo : (180 : ℝ) ≤ L) (hhi : L ≤ (240 : ℝ)) :
    gamma1000RefinedBound L < LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L := by
  have hcheck : LLS.PaperStatements.endpointCorrectionCheck (240) 0 (9) = true := by decide +kernel
  have hcap := (LLS.PaperStatements.endpointCorrectionCheck_sound hcheck).2
  have hcapR : LLS.PaperStatements.fullEndpointEvenGapCorrection (240 : ℝ) ≤ (9 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcap
  have hfirst : LLS.PaperStatements.fullEndpointEvenCorrectionFirstRadius L ≤ (240 : ℝ) := by
    apply max_le (by norm_num only)
    have hcor :=
      LLS.PaperStatements.fullEndpointEvenGapCorrection_gt_16over5
        (by linarith only [hlo] : (8 : ℝ) ≤ L)
    linarith only [hhi, hcor]
  have hB := correction_upper_of_cap (by norm_num only : (8 : ℝ) ≤ 240) hfirst hcapR
  apply gamma_lt_twoStep_of_cap (L₀ := 180) (U := 9) (by linarith only [hlo]) hlo
  · norm_num only
  · norm_num only
  · norm_num only
  · norm_num only [gammaClippedPrefixGap]
  · exact hB

/-- On 120<=L<=240, the refined 1000-prefix Gamma bound is strictly below the two-step
cutoff. Five continuous bands supply correction caps and positive affine gap budgets.
This removes the redundant two-step minimum in the Gamma interval. -/
theorem gamma_lt_twoStep {L : ℝ} (hL : 120 ≤ L) (hU : L ≤ 240) :
    gamma1000RefinedBound L < LLS.PaperStatements.fullEndpointEvenTwoStepCutoff L := by
  by_cases h1 : L ≤ 602 / 5
  · exact gamma_twoStep_band0 hL h1
  · by_cases h2 : L ≤ 122
    · exact gamma_twoStep_band1 (le_of_not_ge h1) h2
    · by_cases h3 : L ≤ 140
      · exact gamma_twoStep_band2 (le_of_not_ge h2) h3
      · by_cases h4 : L ≤ 180
        · exact gamma_twoStep_band3 (le_of_not_ge h3) h4
        · exact gamma_twoStep_band4 (le_of_not_ge h4) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
