/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredPsiLower
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiRange54057

/-! # Centered principal bound at uniform quarter scales -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, certified finite Chebyshev bounds give a centered principal lower bound
on radii from 997/5 to 465/2. Apply the general boundary estimate at `r²`. -/
theorem quarter_combined_finite465 (hRH : RiemannHypothesis) {r : ℝ} (hr : (997 / 5 : ℝ) ≤ r)
    (hu : r ≤ (465 / 2 : ℝ)) :
    (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 7 / 200 - (29631 / 200 : ℝ) / r) -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / r ^ 2) / r ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) (r ^ 2) n).re := by
  have hlo : (39760 : ℝ) ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 997 / 5)]
  have hhi : r ^ 2 < (54057 : ℝ) := by nlinarith only [hr, hu, sq_nonneg (r - 465 / 2)]
  exact quarter_combined_of_psi600 hRH (by linarith only [hr]) (psi_lower_39760_54057 hlo hhi)

end PseudoPrime.PrimeTestBounds.MillerRabin
