/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometric decay with polynomial factors

Shifted natural powers multiplied by a geometric sequence of ratio in `[0, 1)` tend to zero.
-/

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For `0 ≤ r < 1` and fixed natural degree `k`, `(m + 1)^k * r^m` tends to zero.
The proof bounds the shifted power by a constant multiple of `m^k + 1` and applies geometric
decay. This supplies limit estimates for sequences with polynomial growth. -/
theorem tendsto_add_one_pow_mul_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ k * r ^ m) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun m : ℕ => (m : ℝ) ^ k * r ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one k hr h'r
  have h2 : Filter.Tendsto (fun m : ℕ => r ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr h'r
  have h3 :
    Filter.Tendsto (fun m : ℕ => (2 : ℝ) ^ k * ((m : ℝ) ^ k * r ^ m + r ^ m)) Filter.atTop
      (nhds 0) := by
    simpa only [add_zero, mul_zero] using (h1.add h2).const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero (fun m => by positivity) (fun m => ?_) h3
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    simp only [Nat.cast_zero, zero_add, one_pow, pow_zero, mul_one]
    have h0k : (0 : ℝ) ≤ (0 : ℝ) ^ k := pow_nonneg le_rfl k
    have h2k : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num only)
    nlinarith
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
    have hpow_le : ((m : ℝ) + 1) ^ k ≤ (2 * (m : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) hle k
    rw [mul_pow] at hpow_le
    have hrm_nonneg : (0 : ℝ) ≤ r ^ m := by positivity
    have hprod_le : ((m : ℝ) + 1) ^ k * r ^ m ≤ 2 ^ k * (m : ℝ) ^ k * r ^ m :=
      mul_le_mul_of_nonneg_right hpow_le hrm_nonneg
    nlinarith [hprod_le, mul_nonneg (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) k) hrm_nonneg]

/-- For `0 ≤ r < 1`, `(m + 1)^2 * r^m` tends to zero. This degree-two specialization
of `tendsto_add_one_pow_mul_pow_of_lt_one` is used for quadratic growth bounds. -/
theorem tendsto_add_one_sq_mul_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1) ^ 2 * r ^ m) Filter.atTop (nhds 0) := by
  exact tendsto_add_one_pow_mul_pow_of_lt_one 2 hr h'r

end PseudoPrime.AnalyticNumberTheory.General
