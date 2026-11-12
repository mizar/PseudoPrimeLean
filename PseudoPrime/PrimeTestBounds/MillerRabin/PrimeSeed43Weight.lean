/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Checks
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43WeightStep

/-! # Logarithmic weights through 43 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every scaled integer weight bounds the logarithm of its corresponding
prime. Rational certificates bound the new cutoff values, and monotonicity
handles primes sharing a cutoff. -/
theorem primeSeed43_weight_bounds :
    ∀ p ∈ primeSeed43Primes, Real.log p ≤ (primeSeed43Weight p : ℝ) / 10 := by
  exact primeSeed43_weight_step prime_seed19_weight_bounds

end PseudoPrime.PrimeTestBounds.MillerRabin
