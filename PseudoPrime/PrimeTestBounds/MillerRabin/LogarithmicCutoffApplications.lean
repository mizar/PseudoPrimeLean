/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogarithmicCutoffBounds

/-! # Miller–Rabin applications of the refined logarithmic cutoff

The small-input identity reuses the finite Miller–Rabin certificate. The
large-input comparison gives a concrete range of strict improvement.
The existing declaration namespace is retained for API compatibility.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For 0<L≤12, the minimum of the old squared cutoff and the refined one
equals L². Bound log(L) by log(12)≤5/2, so the refined root is at least L.
This preserves the existing finite Miller–Rabin certificate below level 3000. -/
theorem logarithmicCutoff_min_eq_sq_of_small {L : ℝ} (h0 : 0 < L) (h12 : L ≤ 12) :
    min (L ^ 2) ((logarithmicCutoffRoot L) ^ 2) = L ^ 2 := by
  have hl := Real.log_le_log h0 h12
  have hlog12 : Real.log (12 : ℝ) ≤ (5 / 2 : ℝ) := by
    rw [show (12 : ℝ) = 2 ^ (2 : ℕ) * 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only [Nat.cast_ofNat] at ⊢
    linarith only [Real.log_two_lt_d9, Real.log_three_lt_d9]
  have hroot : L ≤ logarithmicCutoffRoot L := by
    unfold logarithmicCutoffRoot
    linarith only [hl, hlog12]
  exact min_eq_left ((sq_le_sq₀ h0.le (h0.le.trans hroot)).mpr hroot)

/-- For n≥200000 the refined squared logarithmic cutoff is strictly below (log(n))².
The small fractions exp(1)<87/32 and exp(5/2)<61/5 combine with the certified
lower bound log(200000)>61/5. The refined root is positive and smaller than log(n).
This gives a concrete range of strict improvement for the public Miller–Rabin cutoff. -/
theorem logarithmicCutoffRoot_sq_lt_log_sq_of_large {n : ℕ} (hn : 200000 ≤ n) :
    (logarithmicCutoffRoot (Real.log n)) ^ 2 < (Real.log n) ^ 2 := by
  have h1 : Real.exp 1 < (87 / 32 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num only)
  have heq : Real.exp (5 / 2 : ℝ) ^ 2 = Real.exp 1 ^ (5 : ℕ) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    norm_num only
  have hpow := pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num only : (5 : ℕ) ≠ 0)
  have he : Real.exp (5 / 2 : ℝ) < (61 / 5 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 2 (by norm_num only : (0 : ℝ) ≤ 61 / 5)
    rw [heq]
    exact hpow.trans (by norm_num only)
  have hlog : (61 / 5 : ℝ) < Real.log (200000 : ℝ) := by
    rw [show (200000 : ℝ) = 2 ^ (6 : ℕ) * 5 ^ (5 : ℕ) by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat] at ⊢
    linarith only [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hL : (61 / 5 : ℝ) < Real.log n :=
    hlog.trans_le (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hn))
  have hL0 : 0 < Real.log n := lt_trans (by norm_num only : (0 : ℝ) < 61 / 5) hL
  have hll : (5 / 2 : ℝ) < Real.log (Real.log n) := (Real.lt_log_iff_exp_lt hL0).mpr (he.trans hL)
  have ht8 := eight_lt_logarithmicCutoffRoot (show (8 : ℝ) ≤ Real.log n by linarith only [hL])
  have htL : logarithmicCutoffRoot (Real.log n) < Real.log n := by
    unfold logarithmicCutoffRoot
    linarith only [hll]
  exact (sq_lt_sq₀ (by linarith only [ht8]) hL0.le).mpr htL

end PseudoPrime.Analysis
