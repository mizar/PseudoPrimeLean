/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountAbelError
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.Analysis.LogLinearIntegral

/-! # Reciprocal zero sum from a zero-count estimate

Evaluate the main-term integral and the entrance constant in Abel summation.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Evaluate the two-sided zeta zero-count main term and its integral from
`2πe` to `b ≥ 2πe`. The logarithm at the lower endpoint equals one. -/
theorem zeroCount_main_cutoff {b : ℝ} (hb : 2 * Real.pi * Real.exp 1 ≤ b) :
    ((1 / Real.pi) * b * (Real.log b - Real.log (2 * Real.pi) - 1) + 7 / 4) / b +
        (∫ t in (2 * Real.pi * Real.exp 1)..b,
          ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4) / t ^ 2) =
      (Real.log (b / (2 * Real.pi))) ^ 2 / (2 * Real.pi) - 1 / (2 * Real.pi) +
        (7 / 4) / (2 * Real.pi * Real.exp 1) := by
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have hb0 : 0 < b := lt_of_lt_of_le hbase hb
  have hp : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  have hlog : Real.log (2 * Real.pi * Real.exp 1) - Real.log (2 * Real.pi) = 1 := by
    rw [Real.log_mul hp (Real.exp_ne_zero _), Real.log_exp]
    ring
  have h :=
    Analysis.log_linear_div_sq_boundary (k := 1 / Real.pi) (c := Real.log (2 * Real.pi)) (d :=
      7 / 4) hbase hb
  rw [h]
  rw [Real.log_div hb0.ne' hp]
  rw [hlog]
  norm_num only [one_pow, sub_self, mul_zero, add_zero]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Bound the positive entrance terms in the reciprocal zero-sum estimate
by `4/5` using explicit bounds for `π`, `e`, and the entrance logarithm. -/
private theorem reciprocal_entrance_bound :
    (7 / 4 : ℝ) / (2 * Real.pi * Real.exp 1) +
        2 * ((Real.log (2 * Real.pi * Real.exp 1) + 1) / (2 * Real.pi * Real.exp 1)) +
        109 / 480 ≤
      (4 / 5 : ℝ) := by
  have he : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num only at h ⊢
    linarith only [h]
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have hm := mul_le_mul hp he (by norm_num only : (0 : ℝ) ≤ 2718 / 1000) Real.pi_pos.le
  have hH : (17 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by nlinarith only [hm]
  have hH0 : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by linarith only [hH]
  have hlogH : Real.log (2 * Real.pi * Real.exp 1) ≤ (2839 / 1000 : ℝ) := by
    rw [Real.log_mul (ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)) (Real.exp_ne_zero _),
      Real.log_exp]
    linarith only [Analysis.log_two_mul_pi_lt]
  have hinv : (2 * Real.pi * Real.exp 1)⁻¹ ≤ (1 / 17 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hH0 (by norm_num only : (0 : ℝ) < 17)).2 hH
  have hinv0 : 0 ≤ (2 * Real.pi * Real.exp 1)⁻¹ := inv_nonneg.mpr hH0.le
  have hlogterm :
    (Real.log (2 * Real.pi * Real.exp 1) + 1) * (2 * Real.pi * Real.exp 1)⁻¹ ≤
      (3839 / 1000 : ℝ) * (1 / 17 : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right
        (show Real.log (2 * Real.pi * Real.exp 1) + 1 ≤ 3839 / 1000 by linarith only [hlogH]) hinv0
    nlinarith only [hmul, hinv]
  simp only [div_eq_mul_inv]
  linarith only [hinv, hlogterm]

/-- Under RH, a two-sided zero-count error bounded by `2 log t` through `b`
yields a reciprocal-height sum bound with its explicit entrance constant.
The estimate retains the negative main-term correction instead of absorbing it. -/
theorem zeroReciprocal_bound_of_count (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) b,
        |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
          2 * Real.log t) :
    zeroReciprocalSum b ≤
      (Real.log (b / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 4 / 5 - 1 / (2 * Real.pi) := by
  have h0 : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have hM :
    ContinuousOn (fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)
      (Set.Icc (2 * Real.pi * Real.exp 1) b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le h0 ht.1)
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have h := reciprocal_sum_of_count_error hRH hb hM hQ
  rw [zeroCount_main_cutoff hb] at h
  have hc := reciprocal_entrance_bound
  have hb0 : 0 < b := lt_of_lt_of_le h0 hb
  have hbi : 0 ≤ 2 / b := div_nonneg (by norm_num only) hb0.le
  linarith only [h, hc, hbi]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
