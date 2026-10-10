/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
public import PseudoPrime.NumberTheory.Factorization
public import PseudoPrime.NumberTheory.CharacterModulus

/-! The concrete `4 * n` character-modulus application of the general prime-factor API. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For odd natural `n`, the uniform character modulus `4 * n` has one more distinct prime
divisor than `n`. Oddness makes four and `n` coprime; multiplicativity of the distinct-factor
count and the prime-power count for four prove the formula. This translates estimates for
the character modulus back to the original odd input. -/
theorem distinctPrimeFactorCount_characterModulus {n : ℕ} (hn : Odd n) :
    distinctPrimeFactorCount (NumberTheory.characterModulus n) =
      distinctPrimeFactorCount n + 1 := by
  have hfour : ArithmeticFunction.cardDistinctFactors 4 = 1 := by
    rw [show 4 = 2 ^ 2 by norm_num only,
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow Nat.prime_two (by norm_num only)]
  rw [distinctPrimeFactorCount_eq_cardDistinctFactors,
    distinctPrimeFactorCount_eq_cardDistinctFactors, NumberTheory.characterModulus,
    ArithmeticFunction.cardDistinctFactors_mul (NumberTheory.four_coprime_of_odd hn), hfour]
  exact Nat.add_comm 1 (ArithmeticFunction.cardDistinctFactors n)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
