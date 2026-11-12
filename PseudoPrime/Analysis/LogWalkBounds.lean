/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import PseudoPrime.Analysis.LogWalkExecution
import Mathlib.Tactic.LinearCombination

/-! # Fixed-point logarithm increments -/

public section

namespace PseudoPrime.Analysis

/-- For every positive natural `n`, the increment from `log n` to `log(n+1)`
lies between `2/(2n+1)` and `1/n`. The lower bound uses the symmetric
logarithm inequality and the upper bound uses the logarithm tangent bound. -/
theorem log_nat_increment_bounds {n : ℕ} (hn : 0 < n) :
    (2 : ℝ) / (2 * n + 1) ≤ Real.log (n + 1 : ℕ) - Real.log n ∧
      Real.log (n + 1 : ℕ) - Real.log n ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hlog : Real.log (n + 1 : ℕ) - Real.log n = Real.log (1 + 1 / (n : ℝ)) := by
    rw [← Real.log_div hn1.ne' hn0.ne']
    congr 1
    simp only [Nat.cast_add, Nat.cast_one, add_div, div_self hn0.ne', one_div]
  rw [hlog]
  have hi : (0 : ℝ) ≤ 1 / n := div_nonneg (by norm_num only) hn0.le
  constructor
  · have h := Real.le_log_one_add_of_nonneg hi
    have hd1 : (0 : ℝ) < 1 / (n : ℝ) + 2 := by linarith only [hi]
    have hd2 : (0 : ℝ) < 2 * n + 1 := by linarith only [hn0]
    have heq : 2 * (1 / (n : ℝ)) / (1 / (n : ℝ) + 2) = 2 / (2 * n + 1) := by
      apply (div_eq_div_iff hd1.ne' hd2.ne').2
      have hc := mul_inv_cancel₀ hn0.ne'
      simp only [div_eq_mul_inv]
      linear_combination (4 : ℝ) * hc
    rw [← heq]
    exact h
  · have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (n : ℝ) by linarith only [hi])
    linarith only [h]

/-- Integer division rounds down the scaled lower increment, while the
quotient plus one bounds the scaled upper increment. The positive denominator
is the only assumption. -/
theorem log_increment_rounding {S n : ℕ} (hn : 0 < n) :
    ((2 * S / (2 * n + 1) : ℕ) : ℝ) ≤ (S : ℝ) * (2 / (2 * n + 1)) ∧
      (S : ℝ) * (1 / (n : ℝ)) ≤ ((S / n + 1 : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  constructor
  · have h := (Nat.cast_div_le (α := ℝ) (m := 2 * S) (n := 2 * n + 1))
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h
    convert h using 1
    ring
  · have h := Nat.lt_mul_div_succ S hn
    have hc : (S : ℝ) < (n : ℝ) * ((S / n : ℕ) + 1 : ℕ) := by exact_mod_cast h
    rw [mul_comm] at hc
    have hh := (div_lt_iff₀ hn0).2 hc
    have heq : (S : ℝ) * (1 / n) = (S : ℝ) / n := by ring
    rw [heq]
    exact hh.le

/-- One fixed-point update turns lower and upper bounds for `S log n` into
bounds for `S log(n+1)`. Both updates use only natural integer arithmetic. -/
theorem log_increment_fixed_step {S n lo hi : ℕ} (hn : 0 < n) (hlo : (lo : ℝ) ≤ S * Real.log n)
    (hhi : (S : ℝ) * Real.log n ≤ hi) :
    ((lo + 2 * S / (2 * n + 1) : ℕ) : ℝ) ≤ S * Real.log (n + 1 : ℕ) ∧
      (S : ℝ) * Real.log (n + 1 : ℕ) ≤ ((hi + (S / n + 1) : ℕ) : ℝ) := by
  have hlog := log_nat_increment_bounds hn
  have hround := log_increment_rounding (S := S) hn
  have hlow := mul_le_mul_of_nonneg_left hlog.1 (Nat.cast_nonneg S : (0 : ℝ) ≤ S)
  have hupp := mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg S : (0 : ℝ) ≤ S)
  simp only [Nat.cast_add, Nat.cast_one] at hlow hupp hround ⊢
  constructor
  · nlinarith only [hlo, hlow, hround.1]
  · nlinarith only [hhi, hupp, hround.2]

/-- The integer log walk preserves outward-rounded bounds through all `k`
steps from a positive starting point. The proof follows the same tail-recursive
updates as the executable definition and does not inspect a list by index. -/
theorem logWalk_bounds (S n lo hi k : ℕ) (hn : 0 < n) (hlo : (lo : ℝ) ≤ S * Real.log n)
    (hhi : (S : ℝ) * Real.log n ≤ hi) :
    ((logWalk S n lo hi k).1 : ℝ) ≤ S * Real.log (n + k : ℕ) ∧
      (S : ℝ) * Real.log (n + k : ℕ) ≤ (logWalk S n lo hi k).2 := by
  induction k generalizing n lo hi with
  | zero => simpa only [logWalk, Nat.add_zero] using And.intro hlo hhi
  | succ k ih =>
    have h := log_increment_fixed_step (S := S) hn hlo hhi
    have hr := ih (n + 1) _ _ (Nat.zero_lt_succ n) h.1 h.2
    simpa only [logWalk, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 k] using hr

end PseudoPrime.Analysis
