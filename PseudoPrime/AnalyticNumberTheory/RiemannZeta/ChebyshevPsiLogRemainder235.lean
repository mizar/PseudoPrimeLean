/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLogScaleConditions235

/-! # Exponential control of the 23.5-scale remainder -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `L ≥ 47/2`, the cubic remainder majorant divided by `exp(L/2)`
is at most `1/500`. A positive four-term Taylor lower bound propagates the
explicit exponential estimate at the starting point over the half-line. -/
theorem scale235_cubic_remainder_le {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    (5 * L / 18 * (L ^ 2 / 48 + 3 * L / 5 + 6) + 3) / Real.exp (L / 2) ≤ 1 / 500 := by
  have ht : 0 ≤ (L - 47 / 2) / 2 := by linarith only [hL]
  have hsum := Real.sum_le_exp_of_nonneg ht 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
    Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat, pow_zero, pow_succ, zero_add] at hsum
  have hpoly :
    0 ≤ 1 + (L - 47 / 2) / 2 + ((L - 47 / 2) / 2) ^ 2 / 2 + ((L - 47 / 2) / 2) ^ 3 / 6 := by
    have ht2 := sq_nonneg ((L - 47 / 2) / 2)
    have ht3 := mul_nonneg ht ht2
    nlinarith only [ht, ht2, ht3]
  have hsum' :
    1 + (L - 47 / 2) / 2 + ((L - 47 / 2) / 2) ^ 2 / 2 + ((L - 47 / 2) / 2) ^ 3 / 6 ≤
      Real.exp ((L - 47 / 2) / 2) := by
    convert hsum using 1
    ring
  have hbase : (117500 : ℝ) ≤ Real.exp (47 / 4) := by
    have h := exp_half_lower_235 (L := 47 / 2) le_rfl
    norm_num only at h
    exact h
  have heq : Real.exp (L / 2) = Real.exp (47 / 4) * Real.exp ((L - 47 / 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm := mul_le_mul hbase hsum' hpoly (Real.exp_pos (47 / 4)).le
  have ht2 := sq_nonneg ((L - 47 / 2) / 2)
  have ht3 := mul_nonneg ht ht2
  apply (div_le_iff₀ (Real.exp_pos _)).2
  rw [heq]
  nlinarith only [hm, ht, ht2, ht3]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
