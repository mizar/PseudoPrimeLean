/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointCorrectionIntervals

/-! # Four endpoint substitutions with a lower logarithmic threshold -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The third radius max(8,L-H(b)). Its floor retains the correction domain beginning at eight. -/
noncomputable def endpointThirdRadius (L : ℝ) : ℝ :=
  max 8 (L - fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionSecondRadius L))

/-- The fourth radius L-H(c), using the clipped third radius c. Its square is the cutoff. -/
noncomputable def endpointFourthRadius (L : ℝ) : ℝ :=
  L - fullEndpointEvenGapCorrection (endpointThirdRadius L)

/-- The squared fourth radius. A positive endpoint gap supplies witnesses for L>=45/4. -/
noncomputable def endpointFourStepCutoff (L : ℝ) : ℝ :=
  endpointFourthRadius L ^ 2

/-- H(8)<13/4 follows from a sixteen-term rational certificate. This lowers the iteration
threshold. -/
theorem correction_eight_lt : fullEndpointEvenGapCorrection 8 < (13 / 4 : ℝ) := by
  have hc : endpointCorrectionCheck 8 0 (32499 / 10000) = true := by decide +kernel
  have h := (endpointCorrectionCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h]

/-- For L>=45/4, positivity of H shows the first radius is below L. The floor is also below L. -/
theorem correction_first_lt {L : ℝ} (hL : 45 / 4 ≤ L) :
    fullEndpointEvenCorrectionFirstRadius L < L := by
  have hc := fullEndpointEvenGapCorrection_gt_16over5 (by linarith only [hL] : (8 : ℝ) ≤ L)
  exact max_lt (by linarith only [hL]) (by linarith only [hc])

/-- For L>=45/4, the second radius exceeds the first. Use monotonicity or the floor anchor. -/
theorem correction_second_gt {L : ℝ} (hL : 45 / 4 ≤ L) :
    fullEndpointEvenCorrectionFirstRadius L < fullEndpointEvenCorrectionSecondRadius L := by
  have ha8 : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have ham := correction_first_lt hL
  by_cases ha : 8 ≤ L - fullEndpointEvenGapCorrection L
  · have hae : fullEndpointEvenCorrectionFirstRadius L = L - fullEndpointEvenGapCorrection L :=
      max_eq_right ha
    have hm :=
      fullEndpointEvenGapCorrection_strictMonoOn ha8 (by linarith only [hL] : (8 : ℝ) ≤ L) ham
    dsimp only [fullEndpointEvenCorrectionSecondRadius]
    linarith only [hm, hae]
  · have hae : fullEndpointEvenCorrectionFirstRadius L = 8 := max_eq_left (le_of_not_ge ha)
    dsimp only [fullEndpointEvenCorrectionSecondRadius]
    rw [hae]
    linarith only [hL, correction_eight_lt]

/-- If c>=8, c<d and d=L-H(c), the exact gap at d is positive. Factor it and compare H(d)>H(c). -/
theorem endpoint_gap_of_step {L c d : ℝ} (hc : 8 ≤ c) (hcd : c < d)
    (hd : d = L - fullEndpointEvenGapCorrection c) :
    0 < fullEndpointEvenExactComparisonGap L (2096 / 1831) d (Real.log d) := by
  have hd8 := hc.trans hcd.le
  have hm := fullEndpointEvenGapCorrection_strictMonoOn hc hd8 hcd
  rw [fullEndpointEvenExactComparisonGap_eq_denominator_correction hd8]
  exact mul_pos (fullEndpointEvenGapDenominator_pos hd8) (by linarith only [hd, hm])

/-- For L>=45/4, the second radius has positive gap. Apply the generic iteration-step lemma. -/
theorem endpoint_twoStep_gap {L : ℝ} (hL : 45 / 4 ≤ L) :
    0 <
      fullEndpointEvenExactComparisonGap L (2096 / 1831) (fullEndpointEvenCorrectionSecondRadius L)
        (Real.log (fullEndpointEvenCorrectionSecondRadius L)) := by
  exact endpoint_gap_of_step (le_max_left _ _) (correction_second_gt hL) rfl

/-- For L>=45/4, first<=third<second. Compare H at the first, second and ambient radii. -/
theorem endpoint_third_bounds {L : ℝ} (hL : 45 / 4 ≤ L) :
    fullEndpointEvenCorrectionFirstRadius L ≤ endpointThirdRadius L ∧
      endpointThirdRadius L < fullEndpointEvenCorrectionSecondRadius L := by
  have ha8 : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have hab := correction_second_gt hL
  have hb8 := ha8.trans hab.le
  have hbL : fullEndpointEvenCorrectionSecondRadius L < L := by
    linarith only [fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L)]
  have hm1 :=
    fullEndpointEvenGapCorrection_strictMonoOn hb8 (by linarith only [hL] : (8 : ℝ) ≤ L) hbL
  have hm2 := fullEndpointEvenGapCorrection_strictMonoOn ha8 hb8 hab
  constructor
  · apply max_le (le_max_left _ _)
    exact
      (by linarith only [hm1] :
            L - fullEndpointEvenGapCorrection L ≤
              L - fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionSecondRadius L)).trans
        (le_max_right _ _)
  · apply max_lt (ha8.trans_lt hab)
    dsimp only [fullEndpointEvenCorrectionSecondRadius] at hm2 ⊢
    linarith only [hm2]

/-- For L>=45/4, third<fourth<=second. Handle the third-radius floor using H(8)<13/4. -/
theorem endpoint_fourth_bounds {L : ℝ} (hL : 45 / 4 ≤ L) :
    endpointThirdRadius L < endpointFourthRadius L ∧
      endpointFourthRadius L ≤ fullEndpointEvenCorrectionSecondRadius L := by
  have hthird := endpoint_third_bounds hL
  have ha8 : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have hc8 : (8 : ℝ) ≤ endpointThirdRadius L := le_max_left _ _
  have hb8 := ha8.trans (correction_second_gt hL).le
  have hm := fullEndpointEvenGapCorrection_strictMonoOn hc8 hb8 hthird.2
  have hmono := fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn ha8 hc8 hthird.1
  constructor
  · by_cases hc : 8 ≤ L - fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionSecondRadius L)
    · have he :
        endpointThirdRadius L =
          L - fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionSecondRadius L) :=
        max_eq_right hc
      dsimp only [endpointFourthRadius]
      linarith only [hm, he]
    · have he : endpointThirdRadius L = 8 := max_eq_left (le_of_not_ge hc)
      dsimp only [endpointFourthRadius]
      rw [he]
      linarith only [hL, correction_eight_lt]
  · dsimp only [endpointFourthRadius, fullEndpointEvenCorrectionSecondRadius]
    linarith only [hmono]

/-- For L>=45/4, the fourth radius has positive gap. Apply the iteration-step lemma. -/
theorem endpoint_fourStep_gap {L : ℝ} (hL : 45 / 4 ≤ L) :
    0 <
      fullEndpointEvenExactComparisonGap L (2096 / 1831) (endpointFourthRadius L)
        (Real.log (endpointFourthRadius L)) := by
  exact endpoint_gap_of_step (le_max_left _ _) (endpoint_fourth_bounds hL).1 rfl

/-- For L>=45/4, the four-step cutoff is no larger than the two-step cutoff. Square positive
radii. -/
theorem endpoint_fourStep_le_two {L : ℝ} (hL : 45 / 4 ≤ L) :
    endpointFourStepCutoff L ≤ fullEndpointEvenTwoStepCutoff L := by
  have hb := endpoint_fourth_bounds hL
  have hc8 : (8 : ℝ) ≤ endpointThirdRadius L := le_max_left _ _
  exact (sq_le_sq₀ (by linarith only [hc8, hb.1]) (by linarith only [hc8, hb.1, hb.2])).mpr hb.2

/-- Four kernel-checked correction caps at 9,13,16 and 120 control continuous comparison
intervals. -/
theorem endpoint_correction_caps :
    fullEndpointEvenGapCorrection 9 ≤ (69 / 20 : ℝ) ∧
      fullEndpointEvenGapCorrection 13 ≤ (399 / 100 : ℝ) ∧
      fullEndpointEvenGapCorrection 16 ≤ (43 / 10 : ℝ) ∧
      fullEndpointEvenGapCorrection 120 ≤ (36 / 5 : ℝ) := by
  have h9 : endpointCorrectionCheck 9 0 (69 / 20) = true := by decide +kernel
  have h13 : endpointCorrectionCheck 13 0 (399 / 100) = true := by decide +kernel
  have h16 : endpointCorrectionCheck 16 0 (43 / 10) = true := by decide +kernel
  have h120 : endpointCorrectionCheck 120 0 (36 / 5) = true := by decide +kernel
  exact
    ⟨by simpa only [Rat.cast_ofNat, Rat.cast_div] using (endpointCorrectionCheck_sound h9).2, by
      simpa only [Rat.cast_ofNat, Rat.cast_div] using (endpointCorrectionCheck_sound h13).2, by
      simpa only [Rat.cast_ofNat, Rat.cast_div] using (endpointCorrectionCheck_sound h16).2, by
      simpa only [Rat.cast_ofNat, Rat.cast_div] using (endpointCorrectionCheck_sound h120).2⟩

/-- For L>=45/4 with first>8, third>first. Use the inactive first floor and H(second)<H(L). -/
theorem endpoint_third_gt_of_first_gt {L : ℝ} (hL : 45 / 4 ≤ L)
    (ha : 8 < fullEndpointEvenCorrectionFirstRadius L) :
    fullEndpointEvenCorrectionFirstRadius L < endpointThirdRadius L := by
  have hlarge : 8 < L - fullEndpointEvenGapCorrection L :=
    (lt_max_iff.mp ha).resolve_left (lt_irrefl 8)
  have hae : fullEndpointEvenCorrectionFirstRadius L = L - fullEndpointEvenGapCorrection L :=
    max_eq_right_of_lt hlarge
  have ha8 : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have hb8 := ha8.trans (correction_second_gt hL).le
  have hbL : fullEndpointEvenCorrectionSecondRadius L < L := by
    linarith only [fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L)]
  have hm :=
    fullEndpointEvenGapCorrection_strictMonoOn hb8 (by linarith only [hL] : (8 : ℝ) ≤ L) hbL
  exact
    (by linarith only [hae, hm] :
          fullEndpointEvenCorrectionFirstRadius L <
            L - fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionSecondRadius L)).trans_le
      (le_max_right _ _)

/-- For 12<=L<=120, the first radius exceeds eight. Apply three monotone correction caps. -/
theorem endpoint_first_gt_eight {L : ℝ} (hL : 12 ≤ L) (hU : L ≤ 120) :
    8 < fullEndpointEvenCorrectionFirstRadius L := by
  have hm := fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
  have h8 : (8 : ℝ) ≤ L := by linarith only [hL]
  apply lt_of_lt_of_le _ (le_max_right _ _)
  by_cases h13 : L ≤ 13
  · have hc := (hm h8 (by norm_num only : (8 : ℝ) ≤ 13) h13).trans endpoint_correction_caps.2.1
    linarith only [hc, hL]
  · by_cases h16 : L ≤ 16
    · have hc := (hm h8 (by norm_num only : (8 : ℝ) ≤ 16) h16).trans endpoint_correction_caps.2.2.1
      linarith only [hc, h13]
    · have hc := (hm h8 (by norm_num only : (8 : ℝ) ≤ 120) hU).trans endpoint_correction_caps.2.2.2
      linarith only [hc, h16]

/-- For 1147/100<=L<=120, four-step is strictly below two-step. Prove third>first and square. -/
theorem endpoint_fourStep_lt_two {L : ℝ} (hL : 1147 / 100 ≤ L) (hU : L ≤ 120) :
    endpointFourStepCutoff L < fullEndpointEvenTwoStepCutoff L := by
  have hlow : (45 / 4 : ℝ) ≤ L := by linarith only [hL]
  have ha8 : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L := le_max_left _ _
  have hthird : fullEndpointEvenCorrectionFirstRadius L < endpointThirdRadius L := by
    by_cases ha : 8 < fullEndpointEvenCorrectionFirstRadius L
    · exact endpoint_third_gt_of_first_gt hlow ha
    · have hae : fullEndpointEvenCorrectionFirstRadius L = 8 := le_antisymm (le_of_not_gt ha) ha8
      have h12 : L < 12 := by
        by_contra h
        exact ha (endpoint_first_gt_eight (le_of_not_gt h) hU)
      have hb8 := ha8.trans (correction_second_gt hlow).le
      have hb9 : fullEndpointEvenCorrectionSecondRadius L ≤ 9 := by
        linarith only [fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L), h12]
      have hc :=
        (fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn hb8 (by norm_num only : (8 : ℝ) ≤ 9)
              hb9).trans
          endpoint_correction_caps.1
      apply lt_of_lt_of_le _ (le_max_right _ _)
      linarith only [hae, hL, hc]
  have hm :=
    fullEndpointEvenGapCorrection_strictMonoOn ha8
      (le_max_left _ _ : (8 : ℝ) ≤ endpointThirdRadius L) hthird
  change
    fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionFirstRadius L) <
      fullEndpointEvenGapCorrection (endpointThirdRadius L) at hm
  have hdlt : endpointFourthRadius L < fullEndpointEvenCorrectionSecondRadius L := by
    dsimp only [endpointFourthRadius, fullEndpointEvenCorrectionSecondRadius]
    linarith only [hm]
  have hfour := endpoint_fourth_bounds hlow
  have hc8 : (8 : ℝ) ≤ endpointThirdRadius L := le_max_left _ _
  exact
    (sq_lt_sq₀ (by linarith only [hc8, hfour.1]) (by linarith only [hc8, hfour.1, hdlt])).mpr hdlt

/-- On 45/4<=L<=74/5, the two-step cutoff is below the shifted 64/81 quadratic.
The second radius is positive and less than L-16/5; square the rational affine comparison.
This extends the comparison to the lowered iteration threshold. -/
theorem endpoint_twoStep_lt_shifted {L : ℝ} (hLlo : 45 / 4 ≤ L) (hLhi : L ≤ 74 / 5) :
    fullEndpointEvenTwoStepCutoff L < (64 / 81 : ℝ) * (L - 7 / 4) ^ 2 := by
  have hrad := fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L)
  have hcomp : fullEndpointEvenCorrectionSecondRadius L < (8 / 9 : ℝ) * (L - 7 / 4) := by
    nlinarith only [hrad, hLhi]
  have hpos : 0 ≤ fullEndpointEvenCorrectionSecondRadius L := by
    have ha8 : 8 ≤ fullEndpointEvenCorrectionFirstRadius L := by
      unfold fullEndpointEvenCorrectionFirstRadius
      exact le_max_left _ _
    have hab := correction_second_gt hLlo
    linarith only [ha8, hab]
  have htarget : 0 ≤ (8 / 9 : ℝ) * (L - 7 / 4) := by nlinarith only [hLlo]
  have hsquare := (sq_lt_sq₀ hpos htarget).mpr hcomp
  change (fullEndpointEvenCorrectionSecondRadius L) ^ 2 < _
  calc
    (fullEndpointEvenCorrectionSecondRadius L) ^ 2 < ((8 / 9 : ℝ) * (L - 7 / 4)) ^ 2 := hsquare
    _ = (64 / 81 : ℝ) * (L - 7 / 4) ^ 2 := by ring

end PseudoPrime.LLS.PaperStatements
