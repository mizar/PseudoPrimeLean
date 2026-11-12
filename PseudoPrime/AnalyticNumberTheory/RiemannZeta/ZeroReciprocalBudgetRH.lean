/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountAbelBudget
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalCountRH
import PseudoPrime.Analysis.LogBudgetIntegral
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Reciprocal zero sum with the explicit zero-count budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Rational bounds on `π`, `e`, and the cutoff logarithm control the
entrance constant after integrating the sharp zero-count budget. -/
private theorem reciprocal_budget_entrance :
    (7 / 4 : ℝ) / (2 * Real.pi * Real.exp 1) +
          ((3 / 4 : ℝ) * (Real.log (2 * Real.pi * Real.exp 1) + 1) + 16 / 5) /
            (2 * Real.pi * Real.exp 1) +
          1 / (5 * (2 * Real.pi * Real.exp 1) ^ 2) +
          109 / 480 -
        1 / (2 * Real.pi) ≤
      53 / 100 := by
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have hm := mul_le_mul hp he (by norm_num only : (0 : ℝ) ≤ 2718 / 1000) Real.pi_pos.le
  have hH : (17 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by nlinarith only [hm]
  have hH0 : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by linarith only [hH]
  have hlogH : Real.log (2 * Real.pi * Real.exp 1) + 1 ≤ (3839 / 1000 : ℝ) := by
    rw [Real.log_mul (ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)) (Real.exp_ne_zero _),
      Real.log_exp]
    linarith only [Analysis.log_two_mul_pi_lt]
  have hinv : (2 * Real.pi * Real.exp 1)⁻¹ ≤ (1 / 17 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hH0 (by norm_num only : (0 : ℝ) < 17)).2 hH
  have hi0 : 0 ≤ (2 * Real.pi * Real.exp 1)⁻¹ := inv_nonneg.mpr hH0.le
  have hi2 : (2 * Real.pi * Real.exp 1)⁻¹ ^ 2 ≤ (1 / 17 : ℝ) ^ 2 := by nlinarith only [hinv, hi0]
  have hprod := mul_le_mul_of_nonneg_right hlogH hi0
  have hpi : (7 / 44 : ℝ) ≤ (2 * Real.pi)⁻¹ := by
    have h :=
      (inv_le_inv₀ (by norm_num only : (0 : ℝ) < 44 / 7) (mul_pos (by norm_num only) Real.pi_pos)).2
        (show 2 * Real.pi ≤ 44 / 7 by linarith only [Real.pi_lt_d4])
    norm_num only at h ⊢
    exact h
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow] at hinv hi0 hi2 hprod hpi ⊢
  nlinarith only [hinv, hi2, hprod, hpi]

/-- Under RH, the reciprocal sum of nonzero zeta-zero ordinates through `b`
is at most `log(b / (2π))² / (2π) + 53/100` for `b ≥ 2πe`. The proof
integrates the explicit zero-count budget and bounds its entrance constant. -/
theorem zeroReciprocal_bound053_of_RH (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b) :
    zeroReciprocalSum b ≤ Real.log (b / (2 * Real.pi)) ^ 2 / (2 * Real.pi) + 53 / 100 := by
  have h0 : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have hb0 : 0 < b := h0.trans_le hb
  have hM :
    ContinuousOn (fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)
      (Set.Icc (2 * Real.pi * Real.exp 1) b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le h0 ht.1)
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hE :
    ContinuousOn (fun t : ℝ ↦ (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t)
      (Set.Icc (2 * Real.pi * Real.exp 1) b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le h0 ht.1)
    exact
      (((continuousAt_const.mul (Real.continuousAt_log ht0)).add continuousAt_const).add
          (continuousAt_const.div continuousAt_id ht0)).continuousWithinAt
  have hQ :
    ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) b,
      |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
        (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t := by
    intro t ht
    have h := zero_count_budget_of_RH hRH ht.1
    convert h using 1
    ring
  have hs := reciprocal_sum_le_of_error hRH hb hM hE hQ
  rw [zeroCount_main_cutoff hb, Analysis.log_budget_div_sq_boundary h0 hb] at hs
  have hc := reciprocal_budget_entrance
  have hb17 : (17 : ℝ) ≤ b := by
    have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
    have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have hm := mul_le_mul hp he (by norm_num only : (0 : ℝ) ≤ 2718 / 1000) Real.pi_pos.le
    nlinarith only [hm, hb]
  have hbi : b⁻¹ ≤ (1 / 17 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hb0 (by norm_num only : (0 : ℝ) < 17)).2 hb17
  have hbi0 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb0.le
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow] at hs hc ⊢
  nlinarith only [hs, hc, hbi, hbi0]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
