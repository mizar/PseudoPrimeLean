/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSharpEnvelope

/-! # Continuous correction comparisons -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For y>=8, the endpoint correction is at most 2 log y+6. Bound log squared by
4y and factor the remaining numerator into nonnegative terms. This controls large radii. -/
theorem correction_log_upper {y : ℝ} (hy : 8 ≤ y) :
    fullEndpointEvenGapCorrection y ≤ 2 * Real.log y + 6 := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hlog := Real.log_le_rpow_div hy0 (by norm_num only : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hsq : (Real.log y) ^ 2 ≤ 4 * y := by
    have hs :=
      (sq_le_sq₀ hz (by linarith only [Real.sqrt_nonneg y] : (0 : ℝ) ≤ Real.sqrt y / (1 / 2))).mpr
        hlog
    nlinarith only [hs, Real.sq_sqrt hy0]
  have hu : 0 ≤ y - 8 := by linarith only [hy]
  have hfactor : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy]
  have hid :
    (2 * Real.log y + 6) * endpointCorrectionDen y (Real.log y) -
        endpointCorrectionNum y (Real.log y) =
      36620000 * (y ^ 2 - 1) * (4 * y - (Real.log y) ^ 2) + 20129471 * (y - 8) ^ 3 +
        183239901 * (y - 8) ^ 2 * Real.log y +
        582189495 * (y - 8) ^ 2 +
        2677026556 * (y - 8) * Real.log y +
        5483968798 * (y - 8) +
        9829442964 * Real.log y +
        16902929326 := by
    dsimp only [endpointCorrectionDen, endpointCorrectionNum]
    ring
  have hmain :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 36620000) hfactor)
      (by linarith only [hsq] : (0 : ℝ) ≤ 4 * y - (Real.log y) ^ 2)
  have h2 := mul_nonneg (sq_nonneg (y - 8)) hz
  have h3 := pow_nonneg hu 3
  have h4 := mul_nonneg hu hz
  rw [endpointCorrection_eq]
  apply (div_le_iff₀ (endpointCorrectionDen_pos hy hz)).mpr
  nlinarith only [hid, hmain, h2, h3, h4, sq_nonneg (y - 8), hu, hz]

/-- For L>=240, the correction is at most L/10. Apply the logarithmic upper
bound and a tangent estimate at 240. This supplies a global fourth-radius lower bound. -/
theorem correction_linear_upper {L : ℝ} (hL : 240 ≤ L) :
    fullEndpointEvenGapCorrection L ≤ L / 10 := by
  have hpos : 0 < L := by linarith only [hL]
  have ht := Analysis.log_le_log_add_sub_div (a := 240) (by norm_num only) hpos
  have hlog : Real.log (240 : ℝ) ≤ 6 := by
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 240) (by norm_num only : (240 : ℝ) ≤ 2 ^ 8)
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_lt_d9]
  have hcor := correction_log_upper (by linarith only [hL] : (8 : ℝ) ≤ L)
  linarith only [ht, hlog, hcor, hL]

/-- For L>=240, C4 is at least 81 L squared/100. Monotonicity bounds the
correction at the third radius by L/10, so the fourth radius is at least 9L/10. -/
theorem fourStep_quadratic_lower {L : ℝ} (hL : 240 ≤ L) :
    (81 / 100 : ℝ) * L ^ 2 ≤ endpointFourStepCutoff L := by
  have hbase : (45 / 4 : ℝ) ≤ L := by linarith only [hL]
  have hc : endpointThirdRadius L < L :=
    (endpoint_third_bounds hbase).2.trans
      (by linarith only [fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L)])
  have hm :=
    fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
      (le_max_left _ _ : (8 : ℝ) ≤ endpointThirdRadius L) (by linarith only [hL] : (8 : ℝ) ≤ L)
      hc.le
  change
    fullEndpointEvenGapCorrection (endpointThirdRadius L) ≤ fullEndpointEvenGapCorrection L at hm
  have hd : (9 / 10 : ℝ) * L ≤ endpointFourthRadius L := by
    dsimp only [endpointFourthRadius]
    linarith only [hm, correction_linear_upper hL]
  have hp : (0 : ℝ) ≤ (9 / 10) * L := by linarith only [hL]
  have hs := (sq_le_sq₀ hp (hp.trans hd)).mpr hd
  dsimp only [endpointFourStepCutoff]
  nlinarith only [hs]

/-- For L>=45/4, the clipped third radius is at most L-16/5. Use H(b)>16/5
and check the floor. This controls correction caps on continuous intervals. -/
theorem third_linear_upper {L : ℝ} (hL : 45 / 4 ≤ L) : endpointThirdRadius L ≤ L - 16 / 5 := by
  have hb :=
    (le_max_left _ _ : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L).trans
      (correction_second_gt hL).le
  have hh := fullEndpointEvenGapCorrection_gt_16over5 hb
  exact max_le (by linarith only [hL]) (by linarith only [hh])

/-- For L>=45/4 and q>=L-16/5 with q>=8, a correction cap H(q)<=U implies
fourth>=L-U. Monotonicity transfers the cap to the clipped third radius. -/
theorem fourth_lower_of_cap {L q U : ℝ} (hL : 45 / 4 ≤ L) (hq : 8 ≤ q) (hcq : L - 16 / 5 ≤ q)
    (hcap : fullEndpointEvenGapCorrection q ≤ U) : L - U ≤ endpointFourthRadius L := by
  have hm :=
    fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
      (le_max_left _ _ : (8 : ℝ) ≤ endpointThirdRadius L) hq ((third_linear_upper hL).trans hcq)
  change
    fullEndpointEvenGapCorrection (endpointThirdRadius L) ≤ fullEndpointEvenGapCorrection q at hm
  dsimp only [endpointFourthRadius]
  linarith only [hm, hcap]

/-- For L>=11.508, third<=L-3.249. A kernel-checked lower certificate at
eight and correction monotonicity provide the bound used near the fixed-prime switch. -/
theorem third_sharp_upper {L : ℝ} (hL : 2877 / 250 ≤ L) :
    endpointThirdRadius L ≤ L - 3249 / 1000 := by
  have h8 : fullEndpointEvenGapCorrection 8 ≥ (3249 / 1000 : ℝ) := by
    have hc : endpointCorrectionCheck 8 (3249 / 1000) (13 / 4) = true := by decide +kernel
    simpa only [Rat.cast_ofNat, Rat.cast_div] using (endpointCorrectionCheck_sound hc).1
  have hb :=
    (le_max_left _ _ : (8 : ℝ) ≤ fullEndpointEvenCorrectionFirstRadius L).trans
      (correction_second_gt (by linarith only [hL] : (45 / 4 : ℝ) ≤ L)).le
  have hm :=
    fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn (by norm_num only : (8 : ℝ) ≤ 8) hb hb
  have hlow :
    (3249 / 1000 : ℝ) ≤ fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionSecondRadius L) :=
    h8.trans hm
  exact max_le (by linarith only [hL]) (by linarith only [hlow])

/-- For L>=11.508, a correction cap above the third radius yields C4>67
when (L-U) squared exceeds 67. Square the nonnegative fourth-radius lower bound. -/
theorem fourStep_gt67_of_cap {L q U : ℝ} (hL : 2877 / 250 ≤ L) (hq : 8 ≤ q)
    (hcq : L - 3249 / 1000 ≤ q) (hcap : fullEndpointEvenGapCorrection q ≤ U) (hpos : 0 ≤ L - U)
    (hsq : 67 < (L - U) ^ 2) : (67 : ℝ) < endpointFourStepCutoff L := by
  have hm :=
    fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn
      (le_max_left _ _ : (8 : ℝ) ≤ endpointThirdRadius L) hq ((third_sharp_upper hL).trans hcq)
  change
    fullEndpointEvenGapCorrection (endpointThirdRadius L) ≤ fullEndpointEvenGapCorrection q at hm
  have hd : L - U ≤ endpointFourthRadius L := by
    dsimp only [endpointFourthRadius]
    linarith only [hm, hcap]
  exact hsq.trans_le ((sq_le_sq₀ hpos (hpos.trans hd)).mpr hd)

/-- For 11.508<=L<=11.75, C4>67. Two rational correction caps at 8.351 and
8.501 cover the full continuous interval. This removes a redundant minimum with 67. -/
theorem fourStep_gt67 {L : ℝ} (hL : 2877 / 250 ≤ L) (hU : L ≤ 47 / 4) :
    (67 : ℝ) < endpointFourStepCutoff L := by
  by_cases h : L ≤ 58 / 5
  · have hc : endpointCorrectionCheck (8351 / 1000) 0 (83 / 25) = true := by decide +kernel
    have hcap : fullEndpointEvenGapCorrection (8351 / 1000 : ℝ) ≤ 83 / 25 := by
      simpa only [Rat.cast_ofNat, Rat.cast_div] using (endpointCorrectionCheck_sound hc).2
    apply fourStep_gt67_of_cap hL (by norm_num only) (by linarith only [h]) hcap
    · linarith only [hL]
    · nlinarith only [hL, sq_nonneg (L - 2877 / 250)]
  · have hc : endpointCorrectionCheck (8501 / 1000) 0 (67 / 20) = true := by decide +kernel
    have hcap : fullEndpointEvenGapCorrection (8501 / 1000 : ℝ) ≤ 67 / 20 := by
      simpa only [Rat.cast_ofNat, Rat.cast_div] using (endpointCorrectionCheck_sound hc).2
    apply fourStep_gt67_of_cap hL (by norm_num only) (by linarith only [hU]) hcap
    · linarith only [hL]
    · have hl : (58 / 5 : ℝ) ≤ L := le_of_not_ge h
      nlinarith only [hl, sq_nonneg (L - 58 / 5)]

end PseudoPrime.LLS.PaperStatements
