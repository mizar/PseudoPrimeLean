/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-! # Finite prime count on an interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the finite interval using the minimum-factor prime test.
/-- The interval `(51023, 51535]` contains exactly 51 primes. The kernel checks
all candidates using the minimum-factor primality test. -/
theorem prime_count_51023_51535 :
    letI : ∀ n : ℕ, Decidable n.Prime := Nat.decidablePrime'
    ((Finset.Ioc 51023 51535).filter Nat.Prime).card = 51 := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
