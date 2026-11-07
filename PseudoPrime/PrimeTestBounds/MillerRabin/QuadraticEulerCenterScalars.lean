/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCenterData

/-! # Refined real scalar bounds for the finite Euler center -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Signed interval arithmetic certifies the weight lower bound, slope
upper bound and integrated main upper bound at 50000. All endpoints are
rational and the kernel verifies their comparisons. -/
theorem center50000_scalar_checks :
    (6716713 / 1000000000000 : ℚ) ≤ Analysis.gammaFiniteEulerLower center50000Ratios ∧
      LLS.gammaFiniteWeightedUpper LLS.gammaSlopeRationalCoefficient center50000Ratios ≤
        (-7106480 / 1000000000000 : ℚ) ∧
      LLS.gammaFiniteWeightedUpper (LLS.gammaTailRationalCoefficient 50000) center50000Ratios ≤
        (7256375 / 1000000 : ℚ) := by
  decide +kernel

/-- The actual Euler weight at the cutoff exceeds its refined positive
lower scalar. Transfer the rational endpoint through ratio soundness. -/
theorem center50000_weight_lower :
    (6716713 / 1000000000000 : ℝ) ≤ Analysis.gammaResolventEulerWeight 50000 := by
  have h := (Rat.cast_le (K := ℝ)).mpr center50000_scalar_checks.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact h.trans center50000_weight_bounds.1

/-- The actual logarithmic slope at the cutoff is below a negative
refined scalar. Preserve the cancellation in its signed node sum. -/
theorem center50000_slope_upper : LLS.gammaEulerLogSlope 50000 ≤ (-(88831 / 12500000000) : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr center50000_scalar_checks.2.1
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] at h
  exact center50000_slope_bounds.2.trans h

/-- The actual integrated Euler main is below its refined upper scalar.
Transfer the signed rational node sum through the real interval theorem. -/
theorem center50000_main_upper : LLS.gammaEulerTailMain 50000 ≤ (58051 / 8000 : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr center50000_scalar_checks.2.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact center50000_tail_main_bounds.2.trans h

end PseudoPrime.PrimeTestBounds.MillerRabin
