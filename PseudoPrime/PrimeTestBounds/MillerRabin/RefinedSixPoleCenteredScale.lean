/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredCombined
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePsiRelativeExact
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleOneSided

/-! # Centered principal comparison at square scale -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `r ≥ 34`, the centered principal comparison uses the relative Chebyshev
window at `r²`. The exact logarithmic atom and the kernel coefficients remain
visible for the subsequent rational bounds. -/
theorem refined_combined_centered_scale (hRH : RiemannHypothesis) {r : ℝ} (hr : 34 ≤ r) :
    let h := (3 / 7 : ℝ) / Real.sqrt r
    let B :=
      (1 / 20 : ℝ) * r * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        (21 / 20 : ℝ) * ((251 / 500) * (27 / 25 : ℝ) ^ 5)
    r * (4 * refinedPrincipalMain 1 - (refinedSixPoleKernel.function (1 / 2)).re) -
        (4 * refinedWeight 1 *
              (h / (19 / 10) * r ^ 2 + (231 / 2500 : ℝ) / h * r + (231 / 2500 : ℝ) / h) +
            3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) +
            5 * B +
            4 * |refinedWeightDeriv 1| * (r / 20 + 21 / 20)) /
          r ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hr0 : 0 < r := (by norm_num only : (0 : ℝ) < 34).trans_le hr
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hp := refined_psi_relative_scale hRH hr
  have hmul :=
    mul_le_mul_of_nonneg_left hp
      (show (0 : ℝ) ≤ 4 * refinedWeight 1 by
        exact mul_nonneg (by norm_num only) refined_unit_weight_nonneg)
  have hnum :
    -(4 * refinedWeight 1 *
          (((3 / 7 : ℝ) / Real.sqrt r) / (19 / 10) * r ^ 2 +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r) * r +
            (231 / 2500 : ℝ) / ((3 / 7 : ℝ) / Real.sqrt r))) ≤
      4 * refinedWeight 1 * (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) := by
    nlinarith only [hmul]
  have hdiv := div_le_div_of_nonneg_right hnum hr0.le
  have h := refined_combined_centered_lower hRH hr2
  simp only [Real.sqrt_sq hr0.le] at h
  dsimp only
  simp only [add_div, sub_div, neg_div] at h hdiv ⊢
  linarith only [h, hdiv]

end PseudoPrime.PrimeTestBounds.MillerRabin
