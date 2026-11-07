/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerUpper
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerPrefixUpper

/-! Certified prefix in the refined Euler upper bound. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, insert the certified prefix upper bound into the Euler-tail estimate at 1000. -/
theorem refined_euler_upper_1000 (hRH : RiemannHypothesis) :
    (∑' m : ℕ, ArithmeticFunction.vonMangoldt m * refinedSixEulerWeight m) <
      (13107 / 5000 : ℝ) + refinedEulerRealWeight 1000 * (1000 - Chebyshev.psi 1000) +
        refinedEulerSlope 1000 *
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1000 - 1000) +
        (∫ t in Set.Ioi (1000 : ℝ), refinedEulerRealWeight t) +
        (1 / 20 : ℝ) * (∫ t in Set.Ioi (1000 : ℝ), Real.sqrt t * refinedEulerVariation t) := by
  have h := refined_euler_centered_upper hRH (a := (1000 : ℝ)) (by norm_num only)
  norm_num only [Nat.floor_ofNat] at h
  linarith only [h, refined_euler_prefix_1000_upper]

end PseudoPrime.PrimeTestBounds.MillerRabin
