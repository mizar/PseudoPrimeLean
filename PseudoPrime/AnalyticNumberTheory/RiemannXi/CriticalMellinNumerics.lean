/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinSplit
import all PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinSplit

/-! # Rational error budget for finite critical-line Mellin integrals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The common finite certificate parameters `N = 8` and `A = 60` give an
analytic truncation error below `10⁻⁵²`. The proof uses the elementary lower
bound `exp 1 > 2`, `π > 3`, and exact rational arithmetic. -/
theorem critical_mellin_error_eight_sixty : criticalMellinError 8 60 ≤ (1 / (10 : ℝ) ^ 52) := by
  have hq : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).2
    linarith only [Real.exp_one_gt_two]
  have h180 : Real.exp (-(180 : ℝ)) ≤ (1 / 2 : ℝ) ^ 180 := by
    calc
      _ = Real.exp (-1) ^ 180 := by
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num only
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hq 180
  have hrat : (1 / 2 : ℝ) ^ 180 ≤ 1 / (10 : ℝ) ^ 54 := by norm_num only
  have he1 : Real.exp (-Real.pi * (81 : ℝ)) ≤ 1 / (10 : ℝ) ^ 54 := by
    have h :=
      Real.exp_le_exp.mpr (show -Real.pi * (81 : ℝ) ≤ -180 by nlinarith only [Real.pi_gt_three])
    exact (h.trans h180).trans hrat
  have he2 : Real.exp (-Real.pi * (60 : ℝ)) ≤ 1 / (10 : ℝ) ^ 54 := by
    have h :=
      Real.exp_le_exp.mpr (show -Real.pi * (60 : ℝ) ≤ -180 by nlinarith only [Real.pi_gt_three])
    exact (h.trans h180).trans hrat
  have hden : 0 < Real.pi * (81 : ℝ) := by nlinarith only [Real.pi_pos]
  have ht1 : 4 * Real.exp (-Real.pi * (81 : ℝ)) / (Real.pi * 81) ≤ 4 / (3 * (10 : ℝ) ^ 54) := by
    apply (div_le_iff₀ hden).2
    nlinarith only [he1, Real.pi_gt_three]
  have ht2 : 16 * Real.exp (-Real.pi * (60 : ℝ)) / Real.pi ≤ 16 / (3 * (10 : ℝ) ^ 54) := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith only [he2, Real.pi_gt_three]
  unfold criticalMellinError
  norm_num only [Nat.cast_ofNat] at ⊢
  nlinarith only [ht1, ht2]

/-- At height `t`, a finite-integral upper bound with rational margin
`10⁻⁵²` proves that xi is positive. The analytic truncation error for
`N = 8` and `A = 60` is absorbed by the rational margin. -/
theorem critical_xi_pos_eight_sixty {t : ℝ}
    (h : (t ^ 2 + 1 / 4) * (criticalCompletedFinite t 8 60 + 1 / (10 : ℝ) ^ 52) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply critical_xi_positive_of_finite (by norm_num only : (1 : ℝ) ≤ 60) 8
  have hp : 0 ≤ t ^ 2 + 1 / 4 := by nlinarith only [sq_nonneg t]
  have hm :=
    mul_le_mul_of_nonneg_left
      (add_le_add_left critical_mellin_error_eight_sixty (criticalCompletedFinite t 8 60)) hp
  linarith only [hm, h]

/-- At height `t`, a finite-integral lower bound with rational margin
`10⁻⁵²` proves that xi is negative. This uses the same certified analytic
error budget and parameters as the positive-sign criterion. -/
theorem critical_xi_neg_eight_sixty {t : ℝ}
    (h : 1 < (t ^ 2 + 1 / 4) * (criticalCompletedFinite t 8 60 - 1 / (10 : ℝ) ^ 52)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply critical_xi_negative_of_finite (by norm_num only : (1 : ℝ) ≤ 60) 8
  have hp : 0 ≤ t ^ 2 + 1 / 4 := by nlinarith only [sq_nonneg t]
  have he :
    criticalCompletedFinite t 8 60 - 1 / (10 : ℝ) ^ 52 ≤
      criticalCompletedFinite t 8 60 - criticalMellinError 8 60 := by
    linarith only [critical_mellin_error_eight_sixty]
  exact h.trans_le (mul_le_mul_of_nonneg_left he hp)

end PseudoPrime.AnalyticNumberTheory.RiemannXi
