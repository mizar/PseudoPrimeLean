/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwiseSteps

/-! # Continuous four-step comparisons for the fixed pointwise improvements -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A test radius with r+H(r)<L lies strictly below the fourth radius.
Strict monotonicity of the correction and the positive fourth-step gap prove this. -/
theorem fourStep_gt_test {L r U b : ℝ} (hL : 45 / 4 ≤ L) (hr : 8 ≤ r)
    (hH : fullEndpointEvenGapCorrection r ≤ U) (hentry : r + U < L) (hb : b < r ^ 2) :
    b < endpointFourStepCutoff L := by
  have hd : (8 : ℝ) < endpointFourthRadius L :=
    (le_max_left _ _).trans_lt (endpoint_fourth_bounds hL).1
  have hg := endpoint_fourStep_gap hL
  rw [fullEndpointEvenExactComparisonGap_eq_denominator_correction hd.le] at hg
  have hf :
    0 < endpointFourthRadius L + fullEndpointEvenGapCorrection (endpointFourthRadius L) - L :=
    pos_of_mul_pos_right hg (fullEndpointEvenGapDenominator_pos hd.le).le
  have hrd : r < endpointFourthRadius L := by
    by_contra hn
    have hmono := fullEndpointEvenGapCorrection_strictMonoOn.monotoneOn hd.le hr (le_of_not_gt hn)
    linarith only [hf, hmono, hH, hentry, le_of_not_gt hn]
  exact
    hb.trans
      ((sq_lt_sq₀ (by linarith only [hr] : (0 : ℝ) ≤ r)
            (by linarith only [hd] : (0 : ℝ) ≤ endpointFourthRadius L)).mpr
        hrd)

/-- From L>=47 / 4, the four-step cutoff strictly exceeds the fixed bound 67.
Use the rational correction certificate at radius 41 / 5. -/
theorem fourStep_step_gt67 {L : ℝ} (hL : 47 / 4 ≤ L) : (67 : ℝ) < endpointFourStepCutoff L := by
  have hc : endpointCorrectionCheck (41 / 5 : ℚ) 0 (33 / 10 : ℚ) = true := by decide +kernel
  have hh := (endpointCorrectionCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
  exact
    fourStep_gt_test (by linarith only [hL]) (by norm_num only) hh (by linarith only [hL])
      (by norm_num only)

/-- From L>=1179 / 100, the four-step cutoff strictly exceeds the fixed bound 71.
Use the rational correction certificate at radius 843 / 100. -/
theorem fourStep_step_gt71 {L : ℝ} (hL : 1179 / 100 ≤ L) : (71 : ℝ) < endpointFourStepCutoff L := by
  have hc : endpointCorrectionCheck (843 / 100 : ℚ) 0 (167 / 50 : ℚ) = true := by decide +kernel
  have hh := (endpointCorrectionCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
  exact
    fourStep_gt_test (by linarith only [hL]) (by norm_num only) hh (by linarith only [hL])
      (by norm_num only)

/-- From L>=1193 / 100, the four-step cutoff strictly exceeds the fixed bound 73.
Use the rational correction certificate at radius 171 / 20. -/
theorem fourStep_step_gt73 {L : ℝ} (hL : 1193 / 100 ≤ L) : (73 : ℝ) < endpointFourStepCutoff L := by
  have hc : endpointCorrectionCheck (171 / 20 : ℚ) 0 (84 / 25 : ℚ) = true := by decide +kernel
  have hh := (endpointCorrectionCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
  exact
    fourStep_gt_test (by linarith only [hL]) (by norm_num only) hh (by linarith only [hL])
      (by norm_num only)

end PseudoPrime.LLS.PaperStatements
