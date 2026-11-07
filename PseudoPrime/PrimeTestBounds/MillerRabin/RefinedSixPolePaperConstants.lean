/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperNecessary

/-! # Certified principal constants for the refined paper bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The unit-cutoff integral exceeds the rational bound required for the paper
coefficient. Use the existing certified upper bound for its exponential denominator. -/
theorem refined_cutoff_lower_precise :
    (33409 / 125000 : ℝ) ≤
      ∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u := by
  rw [refined_six_pole_cutoff, Real.exp_neg, ← one_div]
  have h := one_div_le_one_div_of_le (Real.exp_pos (567 / 200 : ℝ)) refined_six_pole_exp_cutoff
  have hm :=
    mul_le_mul_of_nonneg_left h
      (by norm_num only : (0 : ℝ) ≤ 283259032134555769153731 / 62230388613376000000000)
  norm_num only at hm ⊢
  linarith only [hm]

/-- The kernel half-point value is at most the displayed rational bound. Apply the
existing exponential upper bound with its positive rational coefficient. -/
theorem refined_half_upper_precise :
    (refinedSixPoleKernel.function (1 / 2)).re ≤ (70181 / 200000 : ℝ) := by
  rw [refined_six_pole_half]
  have hm :=
    mul_le_mul_of_nonneg_left refined_six_pole_exp_half
      (by norm_num only : (0 : ℝ) ≤ 22958251200 / 243087455521)
  norm_num only at hm ⊢
  linarith only [hm]

/-- The actual normalized principal gap is strictly greater than the paper constant
`(27/25)^5 * (24439/50000)`. Combine the certified cutoff and half-point bounds. -/
theorem refined_paper_delta_lower :
    (27 / 25 : ℝ) ^ 5 * (24439 / 50000) <
      4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
        (refinedSixPoleKernel.function (1 / 2)).re := by
  have hI := refined_cutoff_lower_precise
  have hT := refined_half_upper_precise
  norm_num only at ⊢
  linarith only [hI, hT]

/-- The unit-cutoff weight is at most `8974/100000`. Evaluate the explicit weight
and apply the certified exponential upper bound. -/
theorem refined_unit_weight_precise : refinedWeight 1 ≤ (8974 / 100000 : ℝ) := by
  have he := refined_exp_neg_unit_le
  norm_num only [refinedWeight, refinedCoord, Real.log_one, Real.sqrt_one, mul_zero, sub_zero,
    mul_one]
  nlinarith only [he]

/-- The square-root boundary cost is strictly below the normalized paper constant
`(27/25)^5 * (53/500)`. Apply the improved unit-weight certificate. -/
theorem refined_paper_sqrt_cost :
    4 * refinedWeight 1 * ((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) <
      (27 / 25 : ℝ) ^ 5 * (53 / 500) := by
  have hw := refined_unit_weight_precise
  norm_num only at ⊢
  linarith only [hw]

end PseudoPrime.PrimeTestBounds.MillerRabin
