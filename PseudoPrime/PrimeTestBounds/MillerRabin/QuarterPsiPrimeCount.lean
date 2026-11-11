/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPsiBound
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Chebyshev lower bounds from prime counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an integer cutoff at least 50000, the certified base bound and primes
above it give a Chebyshev lower bound. Each prime contributes at least 54/5. -/
theorem psi_lower_prime_count {b : ℕ} (hb : 50000 ≤ b) :
    (49985 : ℝ) + (54 / 5 : ℝ) * (((Finset.Ioc 50000 b).filter Nat.Prime).card : ℝ) ≤
      Chebyshev.psi b := by
  classical
  have hlog : (54 / 5 : ℝ) ≤ Real.log 50000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 50000 16 16 (54 / 5) 11 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  have hsub :
    (∑ p ∈ (Finset.Ioc 50000 b).filter Nat.Prime, (54 / 5 : ℝ)) ≤
      ∑ p ∈ Finset.Ioc 50000 b, ArithmeticFunction.vonMangoldt p := by
    calc
      _ ≤ ∑ p ∈ (Finset.Ioc 50000 b).filter Nat.Prime, ArithmeticFunction.vonMangoldt p := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
        rw [ArithmeticFunction.vonMangoldt_apply_prime hp']
        exact
          hlog.trans (Real.log_le_log (by norm_num only) (by exact_mod_cast (Nat.le_of_lt hpgt)))
      _ ≤ ∑ p ∈ Finset.Ioc 50000 b, ArithmeticFunction.vonMangoldt p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro p hp hnot
        exact ArithmeticFunction.vonMangoldt_nonneg
  have he :=
    AnalyticNumberTheory.Arithmetic.mangoldt_interval_sum_eq_psi_sub
      (show (50000 : ℝ) ≤ b by exact_mod_cast hb)
  norm_num only [Nat.floor_ofNat, Nat.floor_natCast] at he
  have hbase := center50000_psi_lower
  simp only [Finset.sum_const, nsmul_eq_mul] at hsub
  linarith only [he, hsub, hbase]

end PseudoPrime.PrimeTestBounds.MillerRabin
