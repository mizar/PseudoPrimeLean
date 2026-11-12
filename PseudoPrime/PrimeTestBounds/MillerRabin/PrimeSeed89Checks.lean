/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Finite prime supply checks through 89 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The labels and positive weights agree with the ordered table. -/
theorem primeSeed89_labels :
    primeSeed89Primes.Nodup ∧
      primeSeed89Primes.map primeSeed89Weight = primeSeed89Weights ∧
      ∀ p ∈ primeSeed89Primes, 0 < primeSeed89Weight p := by
  decide +kernel

/-- Each listed label is prime and at most 89. -/
theorem primeSeed89_prime_supply : ∀ p ∈ primeSeed89Primes, p.Prime ∧ p ≤ 89 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
