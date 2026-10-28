/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSharpEnvelope
public import PseudoPrime.LLS.PaperStatements.ImprovedEnvelopeOrder

/-! # Continuous correction comparisons -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For L>=100, combine a correction cap and a sharper Gamma affine-gap
certificate to prove G1<C4. The comparison is continuous and uses no sampled crossings. -/
theorem sharp_fourStep_cap {L L₀ q U : ℝ} (hL : 100 ≤ L) (hlo : L₀ ≤ L) (hq : 8 ≤ q)
    (hcq : L - 16 / 5 ≤ q) (hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection q ≤ U)
    (hpos : 0 < L₀ - U)
    (hrecip : 0 ≤ (15891 / 25000 : ℝ) * (20475759 / 494000) + (7 / 6) * (15891 / 25000) * U)
    (hanchor : 0 ≤ gammaSharpGap L₀ ((15891 / 25000) * (L₀ - U))) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hd :=
    LLS.PaperStatements.fourth_lower_of_cap (by linarith only [hL] : (45 / 4 : ℝ) ≤ L) hq hcq hcap
  have hs := gammaSharp_lt_affine_sq hL hlo hpos hrecip hanchor
  have hp : 0 ≤ L - U := by linarith only [hlo, hpos]
  exact hs.trans_le ((sq_le_sq₀ hp (hp.trans hd)).mpr hd)

/-- A rational correction cap and affine-gap anchor prove G1<C4 on this closed
subinterval. The finite cap certificate bounds the entire continuous interval. -/
theorem sharp_middle_band0 {L : ℝ} (hlo : (120 : ℝ) ≤ L) (hhi : L ≤ (602 / 5 : ℝ)) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck (586 / 5) 0 (3559 / 500) = true := by
    decide +kernel
  have hcap :
    LLS.PaperStatements.fullEndpointEvenGapCorrection (586 / 5 : ℝ) ≤ (3559 / 500 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  exact
    sharp_fourStep_cap (L₀ := 120) (U := 3559 / 500) (by linarith only [hlo]) hlo (by norm_num only)
      (by linarith only [hhi]) hcap (by norm_num only) (by norm_num only)
      (by norm_num only [gammaSharpGap])

/-- A rational correction cap and affine-gap anchor prove G1<C4 on this closed
subinterval. The finite cap certificate bounds the entire continuous interval. -/
theorem sharp_middle_band1 {L : ℝ} (hlo : (602 / 5 : ℝ) ≤ L) (hhi : L ≤ (122 : ℝ)) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck (594 / 5) 0 (357 / 50) = true := by
    decide +kernel
  have hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection (594 / 5 : ℝ) ≤ (357 / 50 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  exact
    sharp_fourStep_cap (L₀ := 602 / 5) (U := 357 / 50) (by linarith only [hlo]) hlo
      (by norm_num only) (by linarith only [hhi]) hcap (by norm_num only) (by norm_num only)
      (by norm_num only [gammaSharpGap])

/-- A rational correction cap and affine-gap anchor prove G1<C4 on this closed
subinterval. The finite cap certificate bounds the entire continuous interval. -/
theorem sharp_middle_band2 {L : ℝ} (hlo : (122 : ℝ) ≤ L) (hhi : L ≤ (140 : ℝ)) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck (140) 0 (37 / 5) = true := by decide +kernel
  have hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection (140 : ℝ) ≤ (37 / 5 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  exact
    sharp_fourStep_cap (L₀ := 122) (U := 37 / 5) (by linarith only [hlo]) hlo (by norm_num only)
      (by linarith only [hhi]) hcap (by norm_num only) (by norm_num only)
      (by norm_num only [gammaSharpGap])

/-- A rational correction cap and affine-gap anchor prove G1<C4 on this closed
subinterval. The finite cap certificate bounds the entire continuous interval. -/
theorem sharp_middle_band3 {L : ℝ} (hlo : (140 : ℝ) ≤ L) (hhi : L ≤ (180 : ℝ)) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck (180) 0 (8) = true := by decide +kernel
  have hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection (180 : ℝ) ≤ (8 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  exact
    sharp_fourStep_cap (L₀ := 140) (U := 8) (by linarith only [hlo]) hlo (by norm_num only)
      (by linarith only [hhi]) hcap (by norm_num only) (by norm_num only)
      (by norm_num only [gammaSharpGap])

/-- A rational correction cap and affine-gap anchor prove G1<C4 on this closed
subinterval. The finite cap certificate bounds the entire continuous interval. -/
theorem sharp_middle_band4 {L : ℝ} (hlo : (180 : ℝ) ≤ L) (hhi : L ≤ (240 : ℝ)) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  have hc : LLS.PaperStatements.endpointCorrectionCheck (240) 0 (9) = true := by decide +kernel
  have hcap : LLS.PaperStatements.fullEndpointEvenGapCorrection (240 : ℝ) ≤ (9 : ℝ) := by
    simpa only [Rat.cast_ofNat, Rat.cast_div] using
      (LLS.PaperStatements.endpointCorrectionCheck_sound hc).2
  exact
    sharp_fourStep_cap (L₀ := 180) (U := 9) (by linarith only [hlo]) hlo (by norm_num only)
      (by linarith only [hhi]) hcap (by norm_num only) (by norm_num only)
      (by norm_num only [gammaSharpGap])

/-- For 120<=L<=240, G1<C4. Five overlapping closed cap intervals cover
the domain and retain exact rational affine-gap certificates. -/
theorem sharp_lt_fourStep_middle {L : ℝ} (hL : 120 ≤ L) (hU : L ≤ 240) :
    gammaSharpBound L < LLS.PaperStatements.endpointFourStepCutoff L := by
  by_cases h0 : L ≤ 602 / 5
  · exact sharp_middle_band0 hL h0
  by_cases h1 : L ≤ 122
  · exact sharp_middle_band1 (le_of_not_ge h0) h1
  by_cases h2 : L ≤ 140
  · exact sharp_middle_band2 (le_of_not_ge h1) h2
  by_cases h3 : L ≤ 180
  · exact sharp_middle_band3 (le_of_not_ge h2) h3
  exact sharp_middle_band4 (le_of_not_ge h3) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
