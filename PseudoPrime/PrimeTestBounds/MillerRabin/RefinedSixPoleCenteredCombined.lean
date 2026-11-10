/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredFull

/-! # A joint lower bound for the centered principal sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The two centered integrals and the boundary error together cost at most
the displayed variation bounds under RH. The exact Chebyshev boundary and
logarithmic atom remain available for the sharper scale-dependent estimate. -/
theorem refined_combined_centered_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let B :=
      (1 / 20 : ℝ) * Real.sqrt x * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
        (21 / 20 : ℝ) * ((251 / 500) * (27 / 25 : ℝ) ^ 5)
    Real.sqrt x * (4 * refinedPrincipalMain 1 - (refinedSixPoleKernel.function (1 / 2)).re) +
        (4 * refinedWeight 1 * (Chebyshev.psi x - x + Real.log (2 * Real.pi)) -
            3 * Real.log (2 * Real.pi) * refinedWeight (1 / x) -
            5 * B -
            4 * |refinedWeightDeriv 1| * (Real.sqrt x / 20 + 21 / 20)) /
          Real.sqrt x ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hb : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have hunit := abs_le.mp (refined_centered_integral_bound hRH hx zero_le_one hb)
  have hfull := abs_le.mp (refined_centered_integral_bound hRH hx (Real.exp_pos _).le le_rfl)
  have he := LLS.clippedShiftError_abs_le hRH hx0 (show (0 : ℝ) ≤ 1 by norm_num only)
  simp only [mul_one] at he
  have hp :
    refinedWeightDeriv 1 * LLS.clippedShiftError x 1 ≤
      |refinedWeightDeriv 1| * (Real.sqrt x / 20 + 21 / 20) := by
    calc
      _ ≤ |refinedWeightDeriv 1 * LLS.clippedShiftError x 1| := le_abs_self _
      _ = |refinedWeightDeriv 1| * |LLS.clippedShiftError x 1| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left he (abs_nonneg _)
  have hnum :
    4 * refinedWeight 1 * (Chebyshev.psi x - x + Real.log (2 * Real.pi)) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / x) -
        5 *
          ((1 / 20 : ℝ) * Real.sqrt x * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
            (21 / 20 : ℝ) * ((251 / 500) * (27 / 25 : ℝ) ^ 5)) -
        4 * |refinedWeightDeriv 1| * (Real.sqrt x / 20 + 21 / 20) ≤
      4 * (∫ u : ℝ in (0 : ℝ)..1, LLS.clippedShiftError x u * refinedSecondDensity u) -
            (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ),
              LLS.clippedShiftError x u * refinedSecondDensity u) -
            4 * refinedWeightDeriv 1 * LLS.clippedShiftError x 1 +
          4 * refinedWeight 1 * (Chebyshev.psi x - x + Real.log (2 * Real.pi)) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / x) := by
    linarith only [hunit.1, hfull.2, hp]
  have hdiv := div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg x)
  rw [refined_combined_centered_identity hx]
  linarith only [hdiv]

end PseudoPrime.PrimeTestBounds.MillerRabin
