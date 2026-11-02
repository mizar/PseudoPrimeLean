/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellChecks

/-! # First low semiprime cell using repeated prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A semiprime in the first low cell, with the larger factor in the
large-`q` branch, has an MR rejecting prime within the four-ninths bound.
Six primes up to 13 give 28 products with at most two factors; checked
logarithmic intervals establish the closed-cell budgets. -/
theorem exists_prime_witness_first_semiprime_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q)
    (hlo : (83 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2499 / 250)
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb : Analysis.rationalLogIntervalCheck 13 4 12 (2564 / 1000) (2565 / 1000) = true := by
    decide +kernel
  have hc : Analysis.rationalLogIntervalCheck 28 5 12 (33322 / 10000) (33323 / 10000) = true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := (83 / 10 : ℚ)) (b := (2499 / 250 : ℚ)) (k := 2) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hs : (2 : ℝ) * Real.log 13 ≤ (2 / 3 : ℝ) * (83 / 10) := by linarith only [h.1]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 13) (M := 6) (k := 2) (by norm_num only)
      (by decide +kernel) (by norm_num only) hlo hhi hqLarge hs
  · norm_num only [Nat.reduceAdd, Nat.choose, Nat.cast_ofNat]
    exact h.2
  · norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
