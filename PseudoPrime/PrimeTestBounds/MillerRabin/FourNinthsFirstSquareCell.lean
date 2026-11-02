/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSquareBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # First low square cell using repeated prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd square with `8.3 ≤ log n ≤ 8.861` has a prime MR rejecting base
within the four-ninths bound. Six primes up to 13 give 84 products with at
most three factors; rational logarithm checks verify the two strict budgets. -/
theorem exists_prime_witness_first_square_cell {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hlo : (83 / 10 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 8861 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h13 : Analysis.rationalLogIntervalCheck 13 4 12 (2564 / 1000) (2565 / 1000) = true := by
    decide +kernel
  have h84 : Analysis.rationalLogIntervalCheck 84 6 12 (44308 / 10000) (44309 / 10000) = true := by
    decide +kernel
  have hl13 := (Analysis.rationalLogIntervalCheck_sound h13).2
  have hl84 := (Analysis.rationalLogIntervalCheck_sound h84).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl13 hl84
  have hsize : (3 : ℝ) * Real.log 13 < Real.log n := by linarith only [hl13, hlo]
  have hcount : Real.log n < 2 * Real.log (Nat.choose (6 + 3) 3 : ℝ) := by
    norm_num only [Nat.reduceAdd, Nat.choose, Nat.cast_ofNat]
    linarith only [hhi, hl84]
  have hsq := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 83 / 10) hlo 2
  have hbound : (13 : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hsq]
  exact
    square_witness_of_multichoose_bounds hn ho hp hp2 hpow (by norm_num only)
      (by decide +kernel : 6 ≤ (13 : ℕ).primeCounting) hsize hcount hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
