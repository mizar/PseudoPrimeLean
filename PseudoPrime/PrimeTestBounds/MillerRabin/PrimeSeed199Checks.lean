/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Finite prime supply checks through 199 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The distinct labels carry the positive weights in the table order. -/
theorem primeSeed199_labels :
    primeSeed199Primes.Nodup ∧
      primeSeed199Primes.map primeSeed199Weight = primeSeed199Weights ∧
      ∀ p ∈ primeSeed199Primes, 0 < primeSeed199Weight p := by
  decide +kernel

/-- Every listed label is prime and at most 199. -/
theorem primeSeed199_prime_supply : ∀ p ∈ primeSeed199Primes, p.Prime ∧ p ≤ 199 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
