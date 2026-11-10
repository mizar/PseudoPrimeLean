/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaSecond

/-! # Digamma reciprocal-square certificate, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational lower bound for 32 consecutive reciprocal-square terms. -/
theorem refined_digamma_square_block2 :
    (516900 / 100000000 : ℝ) ≤
      ∑ n ∈ Finset.range 32, ((79 / 100 : ℝ) + ((n + 64 : ℕ) : ℝ))⁻¹ ^ 2 := by
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_add, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one]

end PseudoPrime.PrimeTestBounds.MillerRabin
