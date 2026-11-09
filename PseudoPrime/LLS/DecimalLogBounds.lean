/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Logarithmic lower bounds for arbitrary decimal exponents -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The natural logarithm of ten is greater than 23/10. Bound exp(23/10)
by exp(1)^2 times a four-term Taylor upper bound at 3/10.
This gives the sharper decimal conversion needed for the new starting point. -/
theorem log_ten_gt_twenty_three_tenths : (23 / 10 : ℝ) < Real.log 10 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num only : (0 : ℝ) < 10)).mpr
  have ht :=
    Analysis.exp_le_taylor_add_two_next (n := 4) (by norm_num only : (0 : ℝ) ≤ 3 / 10)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ht
  have he : Real.exp 1 ≤ (68 / 25 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num only)
  have hs := pow_le_pow_left₀ (Real.exp_pos 1).le he 2
  rw [show (23 / 10 : ℝ) = 2 * 1 + 3 / 10 by norm_num only, Real.exp_add,
    show (2 : ℝ) * 1 = (2 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
  have hm := mul_le_mul hs ht (Real.exp_pos _).le (by norm_num only)
  exact hm.trans_lt (by norm_num only)

/-- A decimal cutoff 10^d≤n gives log n≥(23/10)d.
Use logarithmic monotonicity and the proved lower bound for log 10.
Keep d variable to avoid evaluating enormous natural powers. -/
theorem log_ge_of_pow10_le {n d : ℕ} (hn : 10 ^ d ≤ n) : (23 / 10 : ℝ) * d ≤ Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) d)
      (by exact_mod_cast hn : (10 : ℝ) ^ d ≤ n)
  rw [Real.log_pow] at h
  exact
    (mul_le_mul_of_nonneg_right log_ten_gt_twenty_three_tenths.le (Nat.cast_nonneg d)).trans
      (by simpa only [mul_comm] using h)

/-- A natural decimal lower bound implies A*log 10<=log n.
Keep the exponent symbolic while casting and applying logarithm monotonicity. -/
theorem mul_log_ten_le_of_pow10_le {A n : ℕ} (hN : 10 ^ A ≤ n) :
    (A : ℝ) * Real.log 10 ≤ Real.log n := by
  have hp : 0 < (10 : ℝ) ^ A := pow_pos (by norm_num only) A
  have hc : (10 : ℝ) ^ A ≤ (n : ℝ) := by exact_mod_cast hN
  have h := Real.log_le_log hp hc
  simpa only [Real.log_pow] using h

end PseudoPrime.LLS
