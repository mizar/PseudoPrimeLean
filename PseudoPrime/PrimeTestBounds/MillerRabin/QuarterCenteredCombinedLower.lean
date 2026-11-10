/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCombinedError
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredCombined

/-! # Refined lower bound after combining principal sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the combined finite and full principal sums have a lower bound
with the improved centered variation budget. The exact double-Abel identity
retains the Chebyshev boundary term and the half-point correction. -/
theorem quarter_combined_centered_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x * (4 * refinedPrincipalMain 1 - (refinedSixPoleKernel.function (1 / 2)).re) +
        (4 * refinedWeight 1 * (Chebyshev.psi x - x + Real.log (2 * Real.pi)) -
            3 * Real.log (2 * Real.pi) * refinedWeight (1 / x) -
            ((1 / 20 : ℝ) * Real.sqrt x *
                (3 * ((203 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5) - 2 * (179 / 1000 : ℝ) +
                  4 * |refinedWeightDeriv 1|) +
              (21 / 20 : ℝ) *
                (3 * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) + 2 * |refinedWeightDeriv 1|))) /
          Real.sqrt x ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have h := quarter_centered_combined_error hRH hx
  have hdiv := div_le_div_of_nonneg_right h (Real.sqrt_nonneg x)
  rw [refined_combined_centered_identity hx]
  simp only [add_div, sub_div, neg_div] at hdiv ⊢
  linarith only [hdiv]

end PseudoPrime.PrimeTestBounds.MillerRabin
