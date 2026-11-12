/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTailBudget
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH

/-! # Explicit inverse-square ordinate tail from the RH zero-count budget -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the full inverse-square zero-ordinate tail above `a ≥ 1000`
is bounded by the displayed logarithmic main term and explicit inverse powers.
The estimate preserves all terms of the RH zero-count budget. -/
theorem ordinateTail_budget_of_RH (hRH : RiemannHypothesis) {a : ℝ} (ha : 1000 ≤ a) :
    ordinateTail a ≤
      (Real.log (a / (2 * Real.pi)) + 1) / (Real.pi * a) +
        ((3 / 2 : ℝ) * Real.log a + 271 / 40) / a ^ 2 +
        2 / (3 * a ^ 3) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hbase : 2 * Real.pi * Real.exp 1 ≤ a := by
    have h :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [h, ha]
  apply ordinateTail_le_of_eventually hRH
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  have hb0 : 0 < b := ha0.trans_le hb
  have hM :
    ContinuousOn (fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)
      (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha0.trans_le ht.1)
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hE :
    ContinuousOn (fun t : ℝ ↦ (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t)
      (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (ha0.trans_le ht.1)
    exact
      (((continuousAt_const.mul (Real.continuousAt_log ht0)).add continuousAt_const).add
          (continuousAt_const.div continuousAt_id ht0)).continuousWithinAt
  have hQ :
    ∀ t ∈ Set.Icc a b,
      |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
        (3 / 4 : ℝ) * Real.log t + 16 / 5 + (2 / 5 : ℝ) / t := by
    intro t ht
    have h := zero_count_budget_of_RH hRH (hbase.trans ht.1)
    convert h using 1
    ring
  have h := finite_tail_of_log_budget (by linarith only [ha]) hb hM hE hQ
  have hlog : 0 ≤ Real.log b - Real.log (2 * Real.pi) + 1 := by
    have hp_le : 2 * Real.pi ≤ b := by linarith only [Real.pi_lt_four, ha, hb]
    have hl := Real.log_le_log hp hp_le
    linarith only [hl]
  have ht : 0 ≤ (1 / Real.pi) * (Real.log b - Real.log (2 * Real.pi) + 1) / b :=
    div_nonneg (mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le) hlog) hb0.le
  have hbi : b⁻¹ ≤ (1 : ℝ) := by
    simpa only [inv_one] using
      (inv_le_inv₀ hb0 (by norm_num only : (0 : ℝ) < 1)).2 (by linarith only [ha, hb])
  have hbi0 : 0 ≤ b⁻¹ := inv_nonneg.mpr hb0.le
  rw [Real.log_div ha0.ne' hp.ne']
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow] at h ht ⊢
  nlinarith only [h, ht, hbi, hbi0]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
