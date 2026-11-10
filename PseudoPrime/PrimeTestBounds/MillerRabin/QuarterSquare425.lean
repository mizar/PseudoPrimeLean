/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareCommon
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage414

/-! # Square-factor witnesses on logarithmic scales 20 to 42.5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd integer with a prime-square divisor and logarithm between 20
and 42.5 has a rejecting prime below one quarter of its squared logarithm.
Direct divisors and existing weighted-product stages supply primes at most 89. -/
theorem quarter_square_20_425 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (20 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 85 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hB : (89 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  by_cases h : p ≤ 1054033525
  · obtain ⟨r, hr, hb, hf⟩ := square_reject_le1054 hn ho hp hdiv h
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
  · obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_square_seed89_414 hn ho hp hdiv (square_factor_le_2087485596 hn hdiv hU)
        (square_factor_budget_414 (Nat.succ_le_of_lt (Nat.lt_of_not_ge h)))
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
