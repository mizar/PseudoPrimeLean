/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Finite prime supply checks through 113 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The labels are distinct and match the positive weight list. -/
theorem primeSeed113_labels :
    primeSeed113Primes.Nodup ∧
      primeSeed113Primes.map primeSeed113Weight = primeSeed113Weights ∧
      ∀ p ∈ primeSeed113Primes, 0 < primeSeed113Weight p := by
  decide +kernel

/-- Every listed label is prime and at most 113. -/
theorem primeSeed113_prime_supply : ∀ p ∈ primeSeed113Primes, p.Prime ∧ p ≤ 113 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
