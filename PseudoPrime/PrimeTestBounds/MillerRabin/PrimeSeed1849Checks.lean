/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Prime.Basic

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data

/-! # Primality checks for the additional prime labels -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
/-- The complete supply is duplicate-free and its positive weights match. -/
theorem primeSeed1849_labels :
    primeSeed1849Primes.Nodup ∧
      primeSeed1849Primes.map primeSeed1849Weight = primeSeed1849Weights ∧
      ∀ p ∈ primeSeed1849Primes, 0 < primeSeed1849Weight p := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
