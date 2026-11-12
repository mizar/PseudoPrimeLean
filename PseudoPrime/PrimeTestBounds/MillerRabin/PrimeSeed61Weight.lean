/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Checks
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43WeightStep
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61WeightStep

/-! # Logarithmic weights through 61 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The scaled integer weights dominate the logarithms of their prime labels.
The existing supply handles primes through 43; rational certificates handle
the four new primes. -/
theorem primeSeed61_weight_bounds :
    ∀ p ∈ primeSeed61Primes, Real.log p ≤ (primeSeed61Weight p : ℝ) / 10 := by
  have h43 := primeSeed43_weight_step prime_seed19_weight_bounds
  exact primeSeed61_weight_step h43

end PseudoPrime.PrimeTestBounds.MillerRabin
