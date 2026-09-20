/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors
import PseudoPrime.NumberTheory.Factorization
import PseudoPrime.NumberTheory.CharacterModulus

/-! The concrete `4 * n` character-modulus application of the general prime-factor API. -/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For odd `n`, passing to the uniform modulus `4 * n` adds exactly the prime factor `2`. -/
theorem distinctPrimeFactorCount_characterModulus {n : ℕ} (hn : Odd n) :
    distinctPrimeFactorCount (NumberTheory.characterModulus n) =
      distinctPrimeFactorCount n + 1 := by
  have hfour : ArithmeticFunction.cardDistinctFactors 4 = 1 := by
    rw [show 4 = 2 ^ 2 by norm_num only,
      ArithmeticFunction.cardDistinctFactors_apply_prime_pow Nat.prime_two (by norm_num only)]
  rw [distinctPrimeFactorCount_eq_cardDistinctFactors,
    distinctPrimeFactorCount_eq_cardDistinctFactors, NumberTheory.characterModulus,
    ArithmeticFunction.cardDistinctFactors_mul (NumberTheory.four_coprime_of_odd hn), hfour]
  omega

end PseudoPrime.AnalyticNumberTheory.Arithmetic
