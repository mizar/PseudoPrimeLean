/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellChecks

/-! # Second low square cell using repeated prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd square with `8.861 ≤ log n ≤ 10.211` has a prime MR rejecting
base within the four-ninths bound. Eight primes up to 19 give 165 products
with at most three factors. The rational checks supply the logarithmic budgets
to the common closed-cell witness criterion. -/
theorem exists_prime_witness_second_square_cell {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hlo : (8861 / 1000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 10211 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb : Analysis.rationalLogIntervalCheck 19 4 12 (2944 / 1000) (2945 / 1000) = true := by
    decide +kernel
  have hc : Analysis.rationalLogIntervalCheck 165 7 12 (51059 / 10000) (51060 / 10000) = true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := (8861 / 1000 : ℚ)) (b := (10211 / 1000 : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 19) (M := 8) (k := 3) (by norm_num only)
      (by decide +kernel) (by norm_num only) hlo hhi h.1
  · norm_num only [Nat.reduceAdd, Nat.choose, Nat.cast_ofNat]
    exact h.2
  · norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
