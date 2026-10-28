/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwiseGrowth

/-! # A continuous pointwise window between consecutive primes -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- An eight-term logarithm enclosure makes the left endpoint gap negative.
Monotonicity of the quadratic in its logarithm supplies the actual log comparison. -/
theorem pointwiseWindow_left :
    endpointPointwiseGap (29 / 2) (2096 / 1831) (107 / 10) (Real.log (107 / 10)) < 0 := by
  have hc :
    Analysis.rationalLogIntervalCheck (107 / 10) 3 8 (2370153 / 1000000) (2370325 / 1000000) =
      true := by
    decide +kernel
  have hz := Analysis.rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hz
  have hn : 0 ≤ Real.log (107 / 10 : ℝ) := Real.log_nonneg (by norm_num only)
  have hlogU : Real.log (107 / 10 : ℝ) ≤ 2370325 / 1000000 := by
    norm_num only at hz ⊢
    exact hz.2
  have hs := (sq_le_sq₀ hn (by norm_num only : (0 : ℝ) ≤ 2370325 / 1000000)).mpr hlogU
  have ha : 0 ≤ lowPrimeA (107 / 10) := by norm_num only [lowPrimeA]
  have hb : 0 ≤ lowPrimeB (29 / 2) (107 / 10) := by norm_num only [lowPrimeB, lowPrimeV]
  have hu :
    lowPrimeA (107 / 10) * (2370325 / 1000000) ^ 2 +
        lowPrimeB (29 / 2) (107 / 10) * (2370325 / 1000000) +
        lowPrimeC (29 / 2) (107 / 10) <
      0 := by
    norm_num only [lowPrimeA, lowPrimeB, lowPrimeC, lowPrimeV]
  rw [lowPrime_gap_quad (by norm_num only : (107 / 10 : ℝ) ≠ 0)]
  nlinarith only [mul_le_mul_of_nonneg_left hs ha, mul_le_mul_of_nonneg_left hlogU hb, hu]

/-- An eight-term logarithm enclosure makes the right endpoint gap positive.
The shared pointwise quadratic theorem transports its rational anchor to the actual logarithm. -/
theorem pointwiseWindow_right :
    0 < endpointPointwiseGap 15 (2096 / 1831) (45 / 4) (Real.log (45 / 4)) := by
  have hc :
    Analysis.rationalLogIntervalCheck (45 / 4) 3 8 (2419835 / 1000000) (2420852 / 1000000) =
      true := by
    decide +kernel
  have hz := Analysis.rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hz
  have ha : 0 ≤ lowPrimeA (45 / 4) := by norm_num only [lowPrimeA]
  have hb : 0 ≤ lowPrimeB 15 (45 / 4) := by norm_num only [lowPrimeB, lowPrimeV]
  have hlogL : (2419835 / 1000000 : ℝ) ≤ Real.log (45 / 4) := by
    norm_num only at hz ⊢
    exact hz.1
  apply
    pointwise_gap_from_quad (a := lowPrimeA (45 / 4)) (b := lowPrimeB 15 (45 / 4)) (L := 15) (L₀ :=
      15) (y := 45 / 4) (z₀ := 2419835 / 1000000) le_rfl (by norm_num only) (by norm_num only) hlogL
      ha hb
  · intro z
    rw [lowPrime_gap_quad (by norm_num only : (45 / 4 : ℝ) ≠ 0),
      lowPrime_gap_quad (by norm_num only : (45 / 4 : ℝ) ≠ 0)]
    ring
  · norm_num only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss]

/-- Throughout the real level interval [29/2,15], the inverse cutoff is between
113 and 127. The signed endpoint gaps and monotone inverse give the continuous comparison. -/
theorem pointwiseCutoff_window113 {L : ℝ} (hL : 29 / 2 ≤ L) (hU : L ≤ 15) :
    (113 : ℝ) < pointwiseCutoff L ∧ pointwiseCutoff L < 127 := by
  have hl := pointwiseWindow_left
  have hr := pointwiseWindow_right
  rw [pointwiseGap_eq (by norm_num only : (8 : ℝ) ≤ 107 / 10)] at hl
  rw [pointwiseGap_eq (by norm_num only : (8 : ℝ) ≤ 45 / 4)] at hr
  have hdL := fullEndpointEvenGapDenominator_pos (by norm_num only : (8 : ℝ) ≤ 107 / 10)
  have hdR := fullEndpointEvenGapDenominator_pos (by norm_num only : (8 : ℝ) ≤ 45 / 4)
  have hleft : pointwiseLevel (107 / 10) < L := by
    dsimp only [pointwiseLevel]
    nlinarith only [hl, hdL, hL]
  have hright : L < pointwiseLevel (45 / 4) := by
    dsimp only [pointwiseLevel]
    nlinarith only [hr, hdR, hU]
  have hradU := pointwiseRadius_lt_of_level (by norm_num only : (8 : ℝ) < 45 / 4) hright
  have hs := pointwiseRadius_spec L
  have hradL : (107 / 10 : ℝ) < pointwiseRadius L := by
    by_contra hn
    have hm :=
      pointwiseLevel_strictMonoOn.monotoneOn hs.1 (by norm_num only : (8 : ℝ) ≤ 107 / 10)
        (le_of_not_gt hn)
    exact not_lt.mpr (hs.2.1.trans hm) hleft
  have hsqL :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 107 / 10)
          (by linarith only [hs.1] : (0 : ℝ) ≤ pointwiseRadius L)).mpr
      hradL
  have hsqU :=
    (sq_lt_sq₀ (by linarith only [hs.1] : (0 : ℝ) ≤ pointwiseRadius L)
          (by norm_num only : (0 : ℝ) ≤ 45 / 4)).mpr
      hradU
  dsimp only [pointwiseCutoff]
  constructor <;> nlinarith only [hsqL, hsqU]

end PseudoPrime.LLS.PaperStatements
