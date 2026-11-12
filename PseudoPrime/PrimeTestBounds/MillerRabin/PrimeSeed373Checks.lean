/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Finite prime supply checks through 373 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The distinct labels carry the positive weights in the table order. -/
theorem primeSeed373_labels :
    primeSeed373Primes.Nodup ∧
      primeSeed373Primes.map primeSeed373Weight = primeSeed373Weights ∧
      ∀ p ∈ primeSeed373Primes, 0 < primeSeed373Weight p := by
  decide +kernel

/-- Every listed label is prime and at most 373. -/
theorem primeSeed373_prime_supply : ∀ p ∈ primeSeed373Primes, p.Prime ∧ p ≤ 373 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
