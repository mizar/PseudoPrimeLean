/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics

/-! # Sharper decimal starting value for coefficient 0.8 negative witnesses

The certified bound log(10)>2.30258 converts the existing log threshold
46000 to the smaller decimal starting value 10^19978.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The decimal logarithm exceeds 2.30258. Bound exp(2.30258) by the
certified square of exp(1) and an eight-term Taylor upper bound.
This sharpens the decimal conversion while retaining the analytic log cutoff. -/
theorem log_ten_gt_230258 : (115129 / 50000 : ℝ) < Real.log 10 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num only : (0 : ℝ) < 10)).mpr
  have ht :=
    exp_le_taylor_add_two_next (n := 8) (by norm_num only : (0 : ℝ) ≤ 15129 / 50000)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ht
  have he : Real.exp 1 ≤ (13591409143 / 5000000000 : ℝ) :=
    Real.exp_one_lt_d9.le.trans (by norm_num only)
  have hs := pow_le_pow_left₀ (Real.exp_pos 1).le he 2
  rw [show (115129 / 50000 : ℝ) = 2 * 1 + 15129 / 50000 by norm_num only, Real.exp_add,
    show (2 : ℝ) * 1 = (2 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
  have hm := mul_le_mul hs ht (Real.exp_pos _).le (by norm_num only)
  exact hm.trans_lt (by norm_num only)

/-- For n≥10^19978, log(n)>46000. Compare logarithms of the variable
decimal power and use log(10)>2.30258. The analytic threshold is unchanged;
the sharper decimal conversion improves pointwise and finite-maximum starts. -/
theorem log_nat_gt_46000_of_decimal_19978 {n : ℕ} (hn : 10 ^ 19978 ≤ n) :
    (46000 : ℝ) < Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) 19978)
      (by exact_mod_cast hn : (10 : ℝ) ^ 19978 ≤ n)
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, log_ten_gt_230258]

end PseudoPrime.Analysis
