/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Logarithmic scales for dyadic moment comparisons -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The integer number log₂(n)+1 of dyadic bands is at most 2(1+ln n).
Compare integer and real base-two logarithms and use ln 2≥1/2. This turns
the exact finite band count into the common logarithmic moment scale. -/
theorem log2_succ_le_two_mul_one_add_log (n : ℕ) :
    ((Nat.log2 n + 1 : ℕ) : ℝ) ≤ 2 * (1 + Real.log n) := by
  have hl := Real.log_natCast_nonneg n
  have h₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left h₂ hl
  have hd : Real.log n / Real.log 2 ≤ 2 * Real.log n :=
    (div_le_iff₀ (Real.log_pos (by norm_num only : (1 : ℝ) < 2))).mpr (by nlinarith only [hm])
  have hj := Real.log2_le_logb n
  rw [Real.logb] at hj
  rw [Nat.cast_add, Nat.cast_one]
  linarith only [hj, hd]

/-- For n≥1, the squared logarithmic moment scale is at most 4n.
Use ln n≤sqrt(n) and sqrt(n)≥1 before squaring. This absorbs the two
extra logarithmic powers in the main-term cubic energy alternative. -/
theorem one_add_log_sq_le_four_mul {n : ℕ} (hn : 1 ≤ n) : (1 + Real.log n) ^ 2 ≤ 4 * (n : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn
  have hp : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hn'
  have hl := log_le_sqrt_of_pos hp
  have hs : (1 : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (by norm_num only : (0 : ℝ) ≤ 1) hp.le).mpr (by simpa only [one_pow] using hn')
  have hL : 1 + Real.log n ≤ 2 * Real.sqrt n := by linarith only [hl, hs]
  calc
    _ ≤ (2 * Real.sqrt n) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [Real.log_natCast_nonneg n]) hL 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt hp.le]; ring

end PseudoPrime.Analysis
