/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Finite prime supply checks through 281 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The distinct labels carry the positive weights in the table order. -/
theorem primeSeed281_labels :
    primeSeed281Primes.Nodup ∧
      primeSeed281Primes.map primeSeed281Weight = primeSeed281Weights ∧
      ∀ p ∈ primeSeed281Primes, 0 < primeSeed281Weight p := by
  decide +kernel

/-- Every listed label is prime and at most 281. -/
theorem primeSeed281_prime_supply : ∀ p ∈ primeSeed281Primes, p.Prime ∧ p ≤ 281 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
