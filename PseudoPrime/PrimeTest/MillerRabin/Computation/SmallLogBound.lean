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

namespace PseudoPrime.PrimeTest

/-- Odd composites above one are at least nine, giving a uniform lower bound for the log square. -/
private theorem log_sq_ge_three_of_odd_composite {n : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnNotPrime : ¬ Nat.Prime n) :
    (3 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
  have hn9 : 9 ≤ n := by
    by_contra hlt9
    have hnlt9 : n < 9 := by omega
    interval_cases n <;> first
    | (norm_num at hn; done)
    | (norm_num at hnOdd; done)
    | exact hnNotPrime (by norm_num)
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    lt_trans (by norm_num : (1 : ℝ) < 1.0986122885) Real.log_three_gt_d9
  have hlog9 : (2 : ℝ) < Real.log 9 := by
    calc
      (2 : ℝ) = 2 * 1 := by norm_num
      _ < 2 * Real.log 3 := mul_lt_mul_of_pos_left hlog3 (by norm_num)
      _ = Real.log (3 ^ 2) := by rw [Real.log_pow]; norm_num
      _ = Real.log 9 := by norm_num
  have hn9cast : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn9
  have hlogn : (2 : ℝ) < Real.log (n : ℝ) :=
    hlog9.trans_le (Real.log_le_log (by norm_num) hn9cast)
  have hlognonneg : (0 : ℝ) ≤ Real.log (n : ℝ) :=
    le_trans (by norm_num) hlogn.le
  have hlogsquare : (4 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.log (n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by norm_num) hlognonneg).mpr hlogn.le
  exact le_trans (by norm_num) hlogsquare

/--
The finite interval supplies a base-`2` or base-`3` witness and the odd-composite logarithmic
estimate supplies its bound. This theorem is independent of GRH and accepts any odd exponent
decomposition, which makes it the small-input branch of the logarithmic witness argument.
-/
theorem exists_prime_millerRabin_witness_le_log_sq_of_lt_3000 {n s d : ℕ}
    (hn : 1 < n)
    (hnOdd : Odd n)
    (hnNotPrime : ¬ Nat.Prime n)
    (hdecomp : n - 1 = 2 ^ s * d)
    (hdOdd : Odd d)
    (hlt : n < 3000) :
    ∃ p : ℕ,
      Nat.Prime p ∧
      (p : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 ∧
      (p : ZMod n) ^ d ≠ 1 ∧
      ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  have hlog := log_sq_ge_three_of_odd_composite hn hnOdd hnNotPrime
  rcases base_two_or_three_rejects_of_lt_3000 hn hnOdd hnNotPrime hlt with hbase2 | hbase3
  · refine ⟨2, Nat.prime_two, ?_, ?_⟩
    · exact le_trans (by norm_num) hlog
    · exact not_strongMillerRabinPass_iff.mp
        ((strongMillerRabinWithBase_eq_false_iff_not_pass_decomp
          (n := n) (s := s) (d := d) (a := 2) hn hdecomp hdOdd).1 hbase2)
  · refine ⟨3, by norm_num, hlog, ?_⟩
    exact not_strongMillerRabinPass_iff.mp
      ((strongMillerRabinWithBase_eq_false_iff_not_pass_decomp
        (n := n) (s := s) (d := d) (a := 3) hn hdecomp hdOdd).1 hbase3)

end PseudoPrime.PrimeTest
