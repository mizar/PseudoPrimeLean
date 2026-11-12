/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Finite prime supply checks through 61 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The labels are distinct, their weights match the table, and every weight
is positive. This transfers the checked recurrence to repeated prime products. -/
theorem primeSeed61_labels :
    primeSeed61Primes.Nodup ∧
      primeSeed61Primes.map primeSeed61Weight = primeSeed61Weights ∧
      ∀ p ∈ primeSeed61Primes, 0 < primeSeed61Weight p := by
  decide +kernel

/-- Every listed label is prime and is at most 61. -/
theorem primeSeed61_prime_supply : ∀ p ∈ primeSeed61Primes, p.Prime ∧ p ≤ 61 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
