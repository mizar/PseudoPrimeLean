/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Checks
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199WeightStep

/-! # Logarithmic weights through 199 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Certified scaled weights bound the logarithms of the listed primes. -/
theorem primeSeed199_weight_bounds :
    ∀ p ∈ primeSeed199Primes, Real.log p ≤ (primeSeed199Weight p : ℝ) / 10 := by
  have h43 := primeSeed43_weight_step prime_seed19_weight_bounds
  have h61 := primeSeed61_weight_step h43
  have h89 := primeSeed89_weight_step h61
  have h113 := primeSeed113_weight_step h89
  exact primeSeed199_weight_step h113

end PseudoPrime.PrimeTestBounds.MillerRabin
