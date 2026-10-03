/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.MillerRabin.Computation.Small
import PseudoPrime.Analysis.LogarithmicConstants

/-!
# Logarithmic witness bound for the finite Strong Miller–Rabin range
-/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime base at most `(log n)^2` that fails the strong test using the canonical
two-adic decomposition of `n - 1`. This predicate is the conclusion of the witness bounds. -/
def PrimeMillerRabinWitness (n : ℕ) : Prop :=
  let s := padicValNat 2 (n - 1)
  let d := Nat.divMaxPow (n - 1) 2
  ∃ p : ℕ,
    Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1

/-- Odd composites above one are at least nine, giving a uniform lower bound for the log square. -/
private theorem log_sq_ge_three_of_odd_composite {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnNotPrime : ¬Nat.Prime n) : (3 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
  have hn9 : 9 ≤ n := by
    by_contra hlt9
    have hnlt9 : n < 9 := Nat.lt_of_not_ge hlt9
    interval_cases n <;>
      first
      | (norm_num only at hn; done)
      | (norm_num only at hnOdd; done)
      | exact hnNotPrime (by norm_num only)
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    lt_trans (by norm_num only : (1 : ℝ) < 1.0986122885) Real.log_three_gt_d9
  have hlog9 : (2 : ℝ) < Real.log 9 := by
    calc
      (2 : ℝ) = 2 * 1 := by norm_num only
      _ < 2 * Real.log 3 := mul_lt_mul_of_pos_left hlog3 (by norm_num only)
      _ = Real.log (3 ^ 2) := by
        rw [Real.log_pow]
        norm_num only
      _ = Real.log 9 := by norm_num only
  have hn9cast : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
  have hlogn : (2 : ℝ) < Real.log (n : ℝ) :=
    hlog9.trans_le (Real.log_le_log (by norm_num only) hn9cast)
  have hlognonneg : (0 : ℝ) ≤ Real.log (n : ℝ) := le_trans (by norm_num only) hlogn.le
  have hlogsquare : (4 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num only
      _ ≤ (Real.log (n : ℝ)) ^ 2 := (sq_le_sq₀ (by norm_num only) hlognonneg).mpr hlogn.le
  exact le_trans (by norm_num only) hlogsquare

/-- A small odd composite has a prime strong Miller–Rabin witness below the log-square
bound. The predecessor decomposition is computed by the test itself. -/
theorem exists_prime_millerRabin_witness_le_log_sq_of_lt_3000 {n : ℕ} (hn : 1 < n) (hnOdd : Odd n)
    (hnNotPrime : ¬Nat.Prime n) (hlt : n < 3000) : PrimeMillerRabinWitness n := by
  have hlog := log_sq_ge_three_of_odd_composite hn hnOdd hnNotPrime
  rcases PrimeTest.base_two_or_three_rejects_of_lt_3000 hn hnOdd hnNotPrime hlt with hbase2 | hbase3
  · refine ⟨2, Nat.prime_two, ?_, ?_⟩
    · exact le_trans (by norm_num only) hlog
    · exact
        PrimeTest.not_strongMillerRabinPass_iff.mp
          (PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp hbase2)
  · refine ⟨3, by norm_num only, hlog, ?_⟩
    exact
      PrimeTest.not_strongMillerRabinPass_iff.mp
        (PrimeTest.strongMillerRabinWithBase_eq_false_iff_not_pass.mp hbase3)

end PseudoPrime.PrimeTestBounds.MillerRabin
