/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SharpLogQuadraticRemainder

/-! # An exponential certificate for the retained two-adic logarithmic remainder -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For every y≥94 the remainder (79/2000)y+14+(15/2)log y-2(log y)² is
strictly positive. Below log y=5 factor the quadratic; above it use the
cubic exponential lower bound and two nonnegative squares. This analytic
certificate covers the full half-line without finite interval data. -/
theorem shiftedLogQuadraticRemainder_pos_of_94 {y : ℝ} (hy : 94 ≤ y) :
    0 < (79 / 2000 : ℝ) * y + 14 + (15 / 2 : ℝ) * Real.log y - 2 * (Real.log y) ^ 2 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  by_cases hz5 : Real.log y ≤ 5
  · have hh :=
      mul_nonneg (sub_nonneg.mpr hz5) (show 0 ≤ 2 * Real.log y + 5 / 2 by linarith only [hz])
    nlinarith only [hh, hy]
  · let u := Real.log y - 5
    have hu : 0 ≤ u := by
      dsimp only [u]; linarith only [hz5]
    have he5 : (148 : ℝ) < Real.exp 5 := by
      have hp : (148 : ℝ) < ∑ k ∈ Finset.range 13, (5 : ℝ) ^ k / k.factorial := by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_succ,
          Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Nat.cast_ofNat]
      exact hp.trans_le (Real.sum_le_exp_of_nonneg (by norm_num only) 13)
    have hsum := Real.sum_le_exp_of_nonneg hu 4
    have he : 1 + u + u ^ 2 / 2 + u ^ 3 / 6 ≤ Real.exp u := by
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
        Nat.factorial_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_zero,
        pow_one] at hsum
      linarith only [hsum]
    have hey : (148 : ℝ) * (1 + u + u ^ 2 / 2 + u ^ 3 / 6) ≤ y := by
      calc
        _ ≤ 148 * Real.exp u := mul_le_mul_of_nonneg_left he (by norm_num only)
        _ ≤ Real.exp 5 * Real.exp u := mul_le_mul_of_nonneg_right he5.le (Real.exp_nonneg u)
        _ = Real.exp (5 + u) := (Real.exp_add 5 u).symm
        _ = y := by
          rw [show 5 + u = Real.log y by
              dsimp only [u]; ring,
            Real.exp_log hy0]
    have hu1 := mul_nonneg hu (sq_nonneg (u - 1))
    have hu2 := sq_nonneg (u - 3 / 2)
    dsimp only [u] at hey hu1 hu2
    nlinarith only [hey, hu1, hu2, hu]

end PseudoPrime.Analysis
