/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Data
public import Mathlib.Data.Nat.Prime.Basic

/-! # Finite prime supply checks through 43 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The prime labels are distinct, their weights match the table, and every
weight is positive. These properties transfer the numerical table to products. -/
theorem primeSeed43_labels :
    primeSeed43Primes.Nodup ∧
      primeSeed43Primes.map primeSeed43Weight = primeSeed43Weights ∧
      ∀ p ∈ primeSeed43Primes, 0 < primeSeed43Weight p := by
  decide +kernel

/-- Every listed label is prime and does not exceed the cutoff 43. -/
theorem primeSeed43_prime_supply : ∀ p ∈ primeSeed43Primes, p.Prime ∧ p ≤ 43 := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
