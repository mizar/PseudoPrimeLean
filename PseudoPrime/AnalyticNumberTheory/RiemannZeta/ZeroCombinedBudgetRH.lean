/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalFrom40
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailRetainedRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal40Numerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.Analysis.LogLinearIntegral
import PseudoPrime.Analysis.LogBudgetIntegral

/-! # Combined reciprocal and inverse-square zero budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and `T ≥ 40`, the reciprocal zero sum and `T` times the
inverse-square ordinate tail satisfy the displayed combined bound. The exact
count at `T` cancels before its error is estimated. -/
theorem combined_zero_budget (hRH : RiemannHypothesis) {T : ℝ} (hT : 40 ≤ T) :
    zeroReciprocalSum T + T * ordinateTail T ≤
      ((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) / (2 * Real.pi) +
            2 / 5 -
          (3 / 8 : ℝ) / T +
        1 / (15 * T ^ 2) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hbase : 2 * Real.pi * Real.exp 1 ≤ (40 : ℝ) := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp]
  have hM :
    ContinuousOn (fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)
      (Set.Icc 40 T) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith only [ht.1]
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hE :
    ContinuousOn (fun t : ℝ ↦ (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t)
      (Set.Icc 40 T) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith only [ht.1]
    exact
      (((continuousAt_const.mul (Real.continuousAt_log ht0)).add continuousAt_const).add
          (continuousAt_const.div continuousAt_id ht0)).continuousWithinAt
  have hQ :
    ∀ t ∈ Set.Icc (40 : ℝ) T,
      |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
        (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t := by
    intro t ht
    have h := zero_count_budget_of_RH hRH (hbase.trans ht.1)
    convert h using 1
    ring
  have hS := reciprocal_sum_retain_count hRH hT hM hE hQ
  have hi := mul_inv_cancel₀ hT0.ne'
  have hU :
    T * ordinateTail T ≤
      -zeroCount T / T + (2 / Real.pi) * (Real.log T - Real.log (2 * Real.pi)) +
        ((7 / 4 : ℝ) + (3 / 4 : ℝ) * (Real.log T + 1 / 2) + 16 / 5) / T +
        (4 / 5 : ℝ) / (3 * T ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (ordinateTail_retain_count hRH hT) hT0.le
    convert h using 1
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    linear_combination
      (zeroCount T * T⁻¹ - 2 * Real.pi⁻¹ * (Real.log T - Real.log (2 * Real.pi)) -
          (7 / 4 + (3 / 4 : ℝ) * (Real.log T + 1 / 2) + 16 / 5) * T⁻¹ -
          (4 / 15 : ℝ) * T⁻¹ ^ 2) *
        hi
  have hm :=
    Analysis.log_linear_div_sq_boundary (a := 40) (b := T) (k := 1 / Real.pi) (c :=
      Real.log (2 * Real.pi)) (d := 7 / 4) (by norm_num only) hT
  have he :=
    Analysis.log_budget_div_sq_boundary (a := 40) (b := T) (α := 3 / 4) (β := 16 / 5) (γ := 2 / 5)
      (by norm_num only) hT
  have hK := reciprocal_40_entrance_le
  have hmult :
    (1 / Real.pi) * T * (Real.log T - Real.log (2 * Real.pi) - 1) / T =
      (1 / Real.pi) * (Real.log T - Real.log (2 * Real.pi) - 1) := by
    simp only [div_eq_mul_inv]
    linear_combination (Real.pi⁻¹ * (Real.log T - Real.log (2 * Real.pi) - 1)) * hi
  have hp : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  rw [Real.log_div hT0.ne' hp]
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow] at hS hU hm he hK hmult ⊢
  nlinarith only [hS, hU, hm, he, hK, hmult]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
