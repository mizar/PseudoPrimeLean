/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import PseudoPrime.Combinatorics.StirlingBounds

/-! # Logarithmic upper bound for factorials -/

@[expose] public section

namespace PseudoPrime.Combinatorics

/-- For any natural `k`, the logarithm of `k!` is at most `(k + 1) * log (k + 1) - k`.
Apply the logarithmic sum–integral comparison at `k + 1`, then remove the final logarithmic
term using the factorial recurrence. The bound supplies factorial-based binomial estimates. -/
theorem log_factorial_le (k : ℕ) :
    Real.log (k.factorial : ℝ) ≤ ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) - k := by
  have hx : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have h := Real.sum_log_le hx
  rw [Nat.floor_natCast, Real.sum_log_eq_log_factorial, Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))] at h
  norm_num only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] at h
  linarith only [h]

/-- If `k ≤ M`, the logarithm of `choose M k` is at least
`k * (log ((M + 1 - k) / (k + 1)) + 1) - log (k + 1)`. Bound each descending-factorial term
below by `M + 1 - k` and use the factorial logarithm estimate. This supplies the factorial-based
prime-product count without evaluating a large factorial. -/
theorem log_choose_lower {M k : ℕ} (hk : k ≤ M) :
    (k : ℝ) * (Real.log (((M + 1 - k : ℕ) : ℝ) / ((k : ℝ) + 1)) + 1) - Real.log ((k : ℝ) + 1) ≤
      Real.log (Nat.choose M k : ℝ) := by
  have hb : (0 : ℝ) < ((M + 1 - k : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt (Nat.lt_succ_of_le hk))
  have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hc : (0 : ℝ) < Nat.choose M k := Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hn := Nat.pow_sub_le_descFactorial M k
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hn
  have hr : (((M + 1 - k : ℕ) : ℝ) ^ k) ≤ (k.factorial : ℝ) * Nat.choose M k := by exact_mod_cast hn
  have hl := Real.log_le_log (pow_pos hb k) hr
  rw [Real.log_pow, Real.log_mul hf.ne' hc.ne'] at hl
  rw [Real.log_div hb.ne' (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
  have hfac := log_factorial_le k
  nlinarith only [hl, hfac]

/-- For `1 ≤ k ≤ M`, the displayed expression bounds `log (choose M k)` from below.
Bound the descending factorial by its smallest factor and use the finite-error Stirling
upper bound for `log (k!)`. This retains the half-logarithmic loss in prime-product counts. -/
theorem log_choose_stirling_lower {M k : ℕ} (hk0 : k ≠ 0) (hk : k ≤ M) :
    (k : ℝ) * Real.log (((M + 1 - k : ℕ) : ℝ) / k) + k - Real.log k / 2 -
        Real.log (2 * Real.pi) / 2 -
        1 / (12 * (k : ℝ)) ≤
      Real.log (Nat.choose M k : ℝ) := by
  have hb : (0 : ℝ) < ((M + 1 - k : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt (Nat.lt_succ_of_le hk))
  have hf : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hc : (0 : ℝ) < Nat.choose M k := Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hn := Nat.pow_sub_le_descFactorial M k
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hn
  have hr : (((M + 1 - k : ℕ) : ℝ) ^ k) ≤ (k.factorial : ℝ) * Nat.choose M k := by exact_mod_cast hn
  have hl := Real.log_le_log (pow_pos hb k) hr
  rw [Real.log_pow, Real.log_mul hf.ne' hc.ne'] at hl
  rw [Real.log_div hb.ne' (Nat.cast_ne_zero.mpr hk0)]
  have hfac := log_factorial_stirling_le hk0
  nlinarith only [hl, hfac]

end PseudoPrime.Combinatorics
