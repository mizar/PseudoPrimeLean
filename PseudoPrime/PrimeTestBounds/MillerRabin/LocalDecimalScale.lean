/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Decimal scale estimates used in local Miller-Rabin bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The elementary decimal logarithm bound used to compare local and global scales. -/
theorem log_ten_lt_seven_thirds : Real.log 10 < 7 / 3 := by
  have hExp1 : (27 / 10 : ℝ) < Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hpow : (27 / 10 : ℝ) ^ 7 < Real.exp 1 ^ 7 :=
    pow_lt_pow_left₀ hExp1 (by norm_num only) (by decide : 7 ≠ 0)
  have hexp7 : Real.exp 7 = Real.exp 1 ^ 7 := by
    rw [show (7 : ℝ) = (7 : ℕ) * 1 by norm_num only]
    exact Real.exp_nat_mul 1 7
  have hExp7 : 1000 < Real.exp 7 := by
    rw [hexp7]
    exact (by norm_num only : (1000 : ℝ) < (27 / 10) ^ 7).trans hpow
  have hexpSevenThirds : Real.exp (7 / 3 : ℝ) ^ 3 = Real.exp 7 := by
    rw [← Real.exp_nat_mul (7 / 3 : ℝ) 3]
    congr 1
    norm_num only
  have hExpSevenThirds : 10 < Real.exp (7 / 3 : ℝ) := by
    apply lt_of_pow_lt_pow_left₀ 3 (Real.exp_pos _).le
    rw [hexpSevenThirds]
    norm_num only at hExp7 ⊢
    exact hExp7
  exact (Real.log_lt_iff_lt_exp (by norm_num only)).2 hExpSevenThirds

/-- If n>0 and A*(7/3)<log n, then 10^A<=n.
Compare logarithms using log 10<7/3, keeping exponent A symbolic.
This supplies large decimal cutoffs without evaluating their natural powers. -/
theorem pow10_le_of_log_gt {A n : ℕ} (hn : 0 < n) (hA : (A : ℝ) * (7 / 3) < Real.log n) :
    10 ^ A ≤ n := by
  by_contra h
  have hR : (n : ℝ) ≤ (10 : ℝ) ^ A := by exact_mod_cast (lt_of_not_ge h).le
  have hl := Real.log_le_log (Nat.cast_pos.mpr hn) hR
  rw [Real.log_pow] at hl
  have hu := mul_le_mul_of_nonneg_left log_ten_lt_seven_thirds.le (Nat.cast_nonneg (α := ℝ) A)
  linarith only [hA, hl, hu]

end PseudoPrime.PrimeTestBounds.MillerRabin
