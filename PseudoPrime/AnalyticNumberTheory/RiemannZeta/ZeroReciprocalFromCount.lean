/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountAbelError

/-! # Reciprocal zero sum from a zero-count estimate

Evaluate the main-term integral and the entrance constant in Abel summation.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For positive ordered endpoints, integrate the generic logarithmic
zero-count main term divided by the squared height. Differentiate its explicit
primitive; the parameters are unrestricted real constants. -/
theorem main_integral {a b k c d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (k * t * (Real.log t - c - 1) + d) / t ^ 2) =
      (k / 2 * (Real.log b - c) ^ 2 - k * (Real.log b - c) - d / b) -
        (k / 2 * (Real.log a - c) ^ 2 - k * (Real.log a - c) - d / a) := by
  have hi :
    IntervalIntegrable (fun t : ℝ ↦ (k * t * (Real.log t - c - 1) + d) / t ^ 2) MeasureTheory.volume
      a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hlog := Real.continuousAt_log ht0
    exact
      (((continuousAt_const.mul continuousAt_id).mul
                ((hlog.sub continuousAt_const).sub continuousAt_const)).add
            continuousAt_const |>.div
          (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)).continuousWithinAt
  have hd :
    ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ k / 2 * (Real.log x - c) ^ 2 - k * (Real.log x - c) - d / x)
        ((k * t * (Real.log t - c - 1) + d) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hl := (Real.hasDerivAt_log ht0).sub_const c
    have h1 := ((hl.pow 2).const_mul (k / 2)).sub (hl.const_mul k)
    have h2 := (hasDerivAt_const t d).div (hasDerivAt_id t) ht0
    have h := h1.sub h2
    convert h using 1
    · funext x
      rfl
    · dsimp only [id_eq]
      have hcancel := mul_inv_cancel₀ ht0
      simp only [div_eq_mul_inv, ← inv_pow]
      linear_combination (k * (Real.log t - c - 1) * t⁻¹) * hcancel
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]

/-- Combine the upper endpoint of the generic logarithmic main term with
its inverse-square integral. The upper logarithmic linear terms cancel. -/
theorem main_boundary {a b k c d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (k * b * (Real.log b - c - 1) + d) / b +
        (∫ t in a..b, (k * t * (Real.log t - c - 1) + d) / t ^ 2) =
      k / 2 * ((Real.log b - c) ^ 2 - (Real.log a - c) ^ 2) + k * (Real.log a - c - 1) + d / a := by
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hab)
  have h := main_integral (k := k) (c := c) (d := d) ha hab
  rw [h]
  have hcancel := mul_inv_cancel₀ hb0
  simp only [div_eq_mul_inv]
  linear_combination (k * (Real.log b - c - 1)) * hcancel

/-- Evaluate the two-sided zeta zero-count main term and its integral from
`2πe` to `b ≥ 2πe`. The logarithm at the lower endpoint equals one. -/
theorem main_cutoff {b : ℝ} (hb : 2 * Real.pi * Real.exp 1 ≤ b) :
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
  have h := main_boundary (k := 1 / Real.pi) (c := Real.log (2 * Real.pi)) (d := 7 / 4) hbase hb
  rw [h]
  rw [Real.log_div hb0.ne' hp]
  rw [hlog]
  norm_num only [one_pow, sub_self, mul_zero, add_zero]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Bound the positive entrance terms in the reciprocal zero-sum estimate
by `803/960`. Use explicit bounds for `π`, `e` and the entrance logarithm. -/
theorem cutoff_constant :
    (7 / 4 : ℝ) / (2 * Real.pi * Real.exp 1) +
        2 * ((Real.log (2 * Real.pi * Real.exp 1) + 1) / (2 * Real.pi * Real.exp 1)) +
        109 / 480 ≤
      (803 / 960 : ℝ) := by
  have he : (8 / 3 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num only at h ⊢
    linarith only [h]
  have hp :=
    mul_le_mul Real.pi_gt_three.le he.le (by norm_num only : (0 : ℝ) ≤ 8 / 3) Real.pi_pos.le
  have hH : (16 : ℝ) ≤ 2 * Real.pi * Real.exp 1 := by nlinarith only [hp]
  have hH0 : (0 : ℝ) < 2 * Real.pi * Real.exp 1 := by linarith only [hH]
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    have h := Real.pi_lt_d4
    norm_num only at h ⊢
    linarith only [h]
  have hlogpi : Real.log (2 * Real.pi) < 2 := by
    apply (Real.log_lt_iff_lt_exp (show 0 < 2 * Real.pi by positivity)).2
    have hexp : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num only, Real.exp_add]
      ring
    rw [hexp]
    nlinarith only [hpi, he, sq_nonneg (Real.exp 1 - 8 / 3)]
  have hlogH : Real.log (2 * Real.pi * Real.exp 1) ≤ 3 := by
    rw [Real.log_mul (ne_of_gt (show 0 < 2 * Real.pi by positivity)) (Real.exp_ne_zero _),
      Real.log_exp]
    linarith only [hlogpi]
  have hinv : (2 * Real.pi * Real.exp 1)⁻¹ ≤ (1 / 16 : ℝ) := by
    simpa only [one_div] using (inv_le_inv₀ hH0 (by norm_num only : (0 : ℝ) < 16)).2 hH
  have hinv0 : 0 ≤ (2 * Real.pi * Real.exp 1)⁻¹ := inv_nonneg.mpr hH0.le
  have hlogterm :
    (Real.log (2 * Real.pi * Real.exp 1) + 1) * (2 * Real.pi * Real.exp 1)⁻¹ ≤
      4 * (1 / 16 : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right
        (show Real.log (2 * Real.pi * Real.exp 1) + 1 ≤ 4 by linarith only [hlogH]) hinv0
    nlinarith only [hmul, hinv]
  simp only [div_eq_mul_inv]
  linarith only [hinv, hlogterm]

/-- Under RH, if the two-sided zero count differs from its stated main term
by at most `2 log t` throughout `[2πe, b]`, the reciprocal-height zero sum is
at most `log(b / (2π))² / (2π) + 1`. The zero-count estimate is an explicit
hypothesis; this theorem does not establish it. -/
theorem zeroReciprocal_of_count_error (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) b,
        |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
          2 * Real.log t) :
    zeroReciprocalSum b ≤ (Real.log (b / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1 := by
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
  rw [main_cutoff hb] at h
  have hc := cutoff_constant
  have hpi : 0 ≤ 1 / (2 * Real.pi) :=
    div_nonneg (by norm_num only) (mul_nonneg (by norm_num only) Real.pi_pos.le)
  have hb0 : 0 < b := lt_of_lt_of_le h0 hb
  have hbi : 0 ≤ 2 / b := div_nonneg (by norm_num only) hb0.le
  linarith only [h, hc, hpi, hbi]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
