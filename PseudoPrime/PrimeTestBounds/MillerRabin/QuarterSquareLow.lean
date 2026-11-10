/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareFirst
import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SevenSupply

/-! # Square-factor quarter-bound witnesses from 8 to 9.6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input with a prime-square divisor and logarithm between 8 and 9.6 has
a rejecting prime below the quarter-square cutoff. Two bounded local witnesses cover the range. -/
theorem quarter_square_8_96 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 48 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h845 : Real.log n ≤ 169 / 20
  · exact exists_prime_reject_quarter_square_first hn ho hp hdiv hL h845
  · obtain ⟨r, hr, hb, hf⟩ := exists_prime_reject_square_le17 hn ho hp hdiv (by linarith only [hU])
    have hB : (17 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [le_of_not_ge h845]
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
