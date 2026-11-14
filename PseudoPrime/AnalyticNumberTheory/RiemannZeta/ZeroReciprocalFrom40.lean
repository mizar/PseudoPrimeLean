/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountAbelBudget
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalShift40
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal40Numerics
import PseudoPrime.Analysis.LogLinearIntegral
import PseudoPrime.Analysis.LogBudgetIntegral

/-! # Abel summation from height 40 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, Abel summation from 40 bounds the reciprocal sum while
retaining the exact upper-endpoint count. This form is suited to cancellation
against a matching inverse-square tail bound. -/
theorem reciprocal_sum_retain_count (hRH : RiemannHypothesis) {b : ℝ} {M E : ℝ → ℝ} (hb : 40 ≤ b)
    (hM : ContinuousOn M (Set.Icc 40 b)) (hE : ContinuousOn E (Set.Icc 40 b))
    (hQ : ∀ t ∈ Set.Icc 40 b, |zeroCount t - M t| ≤ E t) :
    zeroReciprocalSum b ≤
      zeroCount b / b + (∫ t in (40 : ℝ)..b, M t / t ^ 2) + (∫ t in (40 : ℝ)..b, E t / t ^ 2) +
        (231 / 5000 : ℝ) * (640401 / 64000) := by
  have h := zeroReciprocal_abel (by norm_num only : (1 : ℝ) < 40) hb
  have hi := count_integral_le_of_error (by norm_num only : (0 : ℝ) < 40) hb hM hE hQ
  have hs := zeroReciprocal_shift40 hRH
  linarith only [h, hi, hs]

/-- Under RH, a continuous zero-count approximation and error budget on
`[40,b]` bound the reciprocal sum at `b`. The shifted height-40 term is
bounded by the total zero mass, without enumerating low zeros. -/
theorem reciprocal_sum_from40_of_error (hRH : RiemannHypothesis) {b : ℝ} {M E : ℝ → ℝ} (hb : 40 ≤ b)
    (hM : ContinuousOn M (Set.Icc 40 b)) (hE : ContinuousOn E (Set.Icc 40 b))
    (hQ : ∀ t ∈ Set.Icc 40 b, |zeroCount t - M t| ≤ E t) :
    zeroReciprocalSum b ≤
      M b / b + (∫ t in (40 : ℝ)..b, M t / t ^ 2) + E b / b + (∫ t in (40 : ℝ)..b, E t / t ^ 2) +
        (231 / 5000 : ℝ) * (640401 / 64000) := by
  have h := reciprocal_interval_le_of_error (by norm_num only : (1 : ℝ) < 40) hb hM hE hQ
  have hs := zeroReciprocal_shift40 hRH
  linarith only [h, hs]

/-- Under RH and `T ≥ 40`, the reciprocal zero sum is bounded by the
explicit logarithmic main term, the height-40 entrance constant and the
endpoint correction. Evaluate both integrals in the RH counting budget. -/
theorem reciprocal_sum_from40_explicit (hRH : RiemannHypothesis) {T : ℝ} (hT : 40 ≤ T) :
    zeroReciprocalSum T ≤
      (1 / Real.pi) / 2 *
              ((Real.log T - Real.log (2 * Real.pi)) ^ 2 -
                (Real.log 40 - Real.log (2 * Real.pi)) ^ 2) +
            (1 / Real.pi) * (Real.log 40 - Real.log (2 * Real.pi) - 1) +
            (7 / 4 : ℝ) / 40 +
            ((3 / 4 : ℝ) * (Real.log 40 + 1) + 16 / 5) / 40 +
            (2 / 5 : ℝ) / (2 * 40 ^ 2) -
          (3 / 4 : ℝ) / T +
        (2 / 5 : ℝ) / (2 * T ^ 2) +
        (231 / 5000 : ℝ) * (640401 / 64000) := by
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
  have h := reciprocal_sum_from40_of_error hRH hT hM hE hQ
  have hm :=
    Analysis.log_linear_div_sq_boundary (a := 40) (b := T) (k := 1 / Real.pi) (c :=
      Real.log (2 * Real.pi)) (d := 7 / 4) (by norm_num only) hT
  have he :=
    Analysis.log_budget_div_sq_boundary (a := 40) (b := T) (α := 3 / 4) (β := 16 / 5) (γ := 2 / 5)
      (by norm_num only) hT
  linarith only [h, hm, he]

/-- Under RH, the reciprocal zero sum at `T ≥ 40` is at most the logarithmic
main term plus `2/5`, retaining the negative endpoint correction. The
height-40 entrance constant is verified by rational logarithm bounds. -/
theorem zeroReciprocal_le_from40 (hRH : RiemannHypothesis) {T : ℝ} (hT : 40 ≤ T) :
    zeroReciprocalSum T ≤
      (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 2 / 5 - (3 / 4 : ℝ) / T +
        1 / (5 * T ^ 2) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  have h := reciprocal_sum_from40_explicit hRH hT
  have hK := reciprocal_40_entrance_le
  rw [Real.log_div hT0.ne' hp]
  norm_num only at h hK ⊢
  simp only [div_eq_mul_inv, mul_inv_rev] at h hK ⊢
  nlinarith only [h, hK]

/-- Under RH and `T ≥ 40`, the reciprocal zero sum is at most the
logarithmic main term plus `2/5`. The explicit endpoint correction is
nonpositive on this range. -/
theorem zeroReciprocal_bound_two_fifths (hRH : RiemannHypothesis) {T : ℝ} (hT : 40 ≤ T) :
    zeroReciprocalSum T ≤ (Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 2 / 5 := by
  have hT0 : 0 < T := by linarith only [hT]
  have ht1 : (1 / 5 : ℝ) / T ≤ 3 / 4 := by
    apply (div_le_iff₀ hT0).2
    linarith only [hT]
  have ht2 := div_le_div_of_nonneg_right ht1 hT0.le
  have ht : -(3 / 4 : ℝ) / T + 1 / (5 * T ^ 2) ≤ 0 := by
    have he : (1 / 5 : ℝ) / T / T = 1 / (5 * T ^ 2) := by ring
    rw [he] at ht2
    have hsub := sub_nonpos.mpr ht2
    convert hsub using 1
    ring
  rw [neg_div] at ht
  have h := zeroReciprocal_le_from40 hRH hT
  linarith only [h, ht]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
