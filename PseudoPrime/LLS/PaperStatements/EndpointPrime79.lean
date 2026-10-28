/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EndpointPrime79
public import PseudoPrime.LLS.PaperStatements.EndpointFiniteProfiles
public import PseudoPrime.LLS.EndpointPointwiseGrowth

/-! # Positive fixed-79 gap and the continuous comparison above prime 83 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The fixed-79 gained gap has nonnegative quadratic coefficients at its cap. -/
theorem prime79_coefficients :
    0 ≤ lowPrimeA Analysis.prime79Radius ∧
      0 ≤
        lowPrimeB Analysis.prime79Cap Analysis.prime79Radius +
          2 * (Analysis.prime79Radius : ℝ) ^ 2 * Analysis.prime79CreditR := by
  norm_num only [lowPrimeA, lowPrimeB, lowPrimeV, Analysis.prime79Radius, Analysis.prime79Cap,
    Analysis.prime79CreditR, Rat.cast_div, Rat.cast_ofNat, and_self]

/-- The fixed-79 gained gap is strictly positive at the lower logarithm anchor. -/
theorem prime79_anchor :
    0 <
      finitePrincipalGap Analysis.prime79Cap (2096 / 1831) Analysis.prime79Radius
        Analysis.prime79LogLo Analysis.prime79CreditR Analysis.prime79CreditS := by
  norm_num only [finitePrincipalGap, endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
    Analysis.pointwiseReciprocalLoss, Analysis.prime79Cap, Analysis.prime79Radius,
    Analysis.prime79LogLo, Analysis.prime79CreditR, Analysis.prime79CreditS, Rat.cast_div,
    Rat.cast_ofNat]

/-- The fixed-79 gained gap is positive at the actual logarithm through its tuned cap. -/
theorem prime79_gap {L : ℝ} (hL : L ≤ Analysis.prime79Cap) :
    0 <
      finitePrincipalGap L (2096 / 1831) Analysis.prime79Radius (Real.log Analysis.prime79Radius)
        Analysis.prime79CreditR Analysis.prime79CreditS := by
  apply
    finitePrincipal_gap_from_quad (a := lowPrimeA Analysis.prime79Radius) (b :=
      lowPrimeB Analysis.prime79Cap Analysis.prime79Radius +
        2 * (Analysis.prime79Radius : ℝ) ^ 2 * Analysis.prime79CreditR)
      hL (by norm_num only [Analysis.prime79Radius, Rat.cast_div, Rat.cast_ofNat])
      (by norm_num only [Analysis.prime79LogLo, Rat.cast_div, Rat.cast_ofNat])
      Analysis.prime79_log_bounds.1 prime79_coefficients.1 prime79_coefficients.2
  · intro z
    dsimp only [finitePrincipalGap]
    rw [lowPrime_gap_quad (by norm_num only [Analysis.prime79Radius, Rat.cast_div, Rat.cast_ofNat]),
      lowPrime_gap_quad (by norm_num only [Analysis.prime79Radius, Rat.cast_div, Rat.cast_ofNat])]
    ring
  · exact prime79_anchor

/-- A rational comparison-log upper bound reuses the single fixed-79 Taylor certificate. -/
def prime79CompareLog : ℚ :=
  Analysis.prime79LogHi + (9111 / 1000) / Analysis.prime79Radius - 1

/-- The elementary log ratio estimate bounds the comparison radius without another Taylor check. -/
theorem prime79_compare_log : Real.log (9111 / 1000 : ℝ) ≤ (prime79CompareLog : ℝ) := by
  have hr :=
    Real.log_le_sub_one_of_pos
      (by norm_num only [Analysis.prime79Radius, Rat.cast_div, Rat.cast_ofNat] :
        (0 : ℝ) < (9111 / 1000) / (Analysis.prime79Radius : ℝ))
  rw [Real.log_div (by norm_num only)
      (by norm_num only [Analysis.prime79Radius, Rat.cast_div, Rat.cast_ofNat])] at hr
  simp only [prime79CompareLog, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one]
  linarith only [hr, Analysis.prime79_log_bounds.2]

/-- The current pointwise gap is strictly negative at the fixed-79 comparison entrance. -/
theorem prime79_compare_negative :
    endpointPointwiseGap (1261 / 100) (2096 / 1831) (9111 / 1000) (Real.log (9111 / 1000 : ℝ)) <
      0 := by
  have hu := prime79_compare_log
  have hz : 0 ≤ Real.log (9111 / 1000 : ℝ) := Real.log_nonneg (by norm_num only)
  have hs := (sq_le_sq₀ hz (hz.trans hu)).mpr hu
  have ha : 0 ≤ lowPrimeA (9111 / 1000) := by norm_num only [lowPrimeA]
  have hb : 0 ≤ lowPrimeB (1261 / 100) (9111 / 1000) := by norm_num only [lowPrimeB, lowPrimeV]
  have hg :
    endpointPointwiseGap (1261 / 100) (2096 / 1831) (9111 / 1000) prime79CompareLog < 0 := by
    norm_num only [endpointPointwiseGap, fullEndpointEvenExactComparisonGap,
      Analysis.pointwiseReciprocalLoss, prime79CompareLog, Analysis.prime79LogHi,
      Analysis.prime79Radius, Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_sub,
      Rat.cast_one]
  rw [lowPrime_gap_quad (by norm_num only : (9111 / 1000 : ℝ) ≠ 0)] at hg ⊢
  nlinarith only [hg, mul_le_mul_of_nonneg_left hs ha, mul_le_mul_of_nonneg_left hu hb]

/-- At every level at least 12.61 the current pointwise cutoff exceeds 83. -/
theorem prime79_pointwise_lower {L : ℝ} (hL : 1261 / 100 ≤ L) : (83 : ℝ) < pointwiseCutoff L := by
  have hg := prime79_compare_negative
  rw [pointwiseGap_eq (by norm_num only : (8 : ℝ) ≤ 9111 / 1000)] at hg
  have hd := fullEndpointEvenGapDenominator_pos (by norm_num only : (8 : ℝ) ≤ 9111 / 1000)
  have hleft : pointwiseLevel (9111 / 1000) < L := by
    dsimp only [pointwiseLevel]
    nlinarith only [hg, hd, hL]
  have hs := pointwiseRadius_spec L
  have hrad : (9111 / 1000 : ℝ) < pointwiseRadius L := by
    by_contra hn
    have hm :=
      pointwiseLevel_strictMonoOn.monotoneOn hs.1 (by norm_num only : (8 : ℝ) ≤ 9111 / 1000)
        (le_of_not_gt hn)
    exact not_lt.mpr (hs.2.1.trans hm) hleft
  have hsq :=
    (sq_lt_sq₀ (by norm_num only : (0 : ℝ) ≤ 9111 / 1000)
          (by linarith only [hs.1] : (0 : ℝ) ≤ pointwiseRadius L)).mpr
      hrad
  dsimp only [pointwiseCutoff]
  nlinarith only [hsq]

end PseudoPrime.LLS.PaperStatements
