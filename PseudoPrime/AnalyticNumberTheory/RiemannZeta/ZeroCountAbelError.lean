/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountInverseSquare

/-! # Integrating a zero-count error bound

Transfer a pointwise logarithmic zero-count error through Abel summation.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For positive ordered endpoints, integrate `log t / t²` using the
antiderivative `-(log t + 1) / t`. This evaluates the zero-count error
contribution in reciprocal Abel summation. -/
theorem integral_log_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t / t ^ 2) = (Real.log a + 1) / a - (Real.log b + 1) / b := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ Real.log t / t ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    exact
      ((Real.continuousAt_log ht0).div ((continuousAt_id).pow 2)
          (pow_ne_zero 2 ht0)).continuousWithinAt
  have hd :
    ∀ t ∈ Set.uIcc a b, HasDerivAt (fun x : ℝ ↦ -(Real.log x + 1) / x) (Real.log t / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have h := ((Real.hasDerivAt_log ht0).add_const 1).neg.div (hasDerivAt_id t) ht0
    have hval : (-t⁻¹ * t - -(Real.log t + 1) * 1) / t ^ 2 = Real.log t / t ^ 2 := by
      have ht1 := inv_mul_cancel₀ ht0
      congr 1
      nlinarith only [ht1]
    convert h using 1
    · funext x
      rfl
    · exact hval.symm
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- If a continuous function `M` approximates the two-sided zero count to
within `2 log t` on `1 < a ≤ t ≤ b`, bound the zero-count integral by the
integral of `M` and an explicit endpoint error. The approximation is an
assumption, not a proof of the explicit zero-count estimate. -/
theorem count_integral_of_error {a b : ℝ} {M : ℝ → ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hM : ContinuousOn M (Set.Icc a b))
    (hQ : ∀ t ∈ Set.Icc a b, |zeroCount t - M t| ≤ 2 * Real.log t) :
    (∫ t in a..b, zeroCount t / t ^ 2) ≤
      (∫ t in a..b, M t / t ^ 2) + 2 * ((Real.log a + 1) / a - (Real.log b + 1) / b) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.Icc a b) := by
    intro t ht
    exact ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le ha0 ht.1))).pow 2) |>.continuousWithinAt
  have hl : ContinuousOn Real.log (Set.Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le ha0 ht.1)
  have hm : IntervalIntegrable (fun t ↦ M t / t ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have h := hM.mul hc
    convert h using 1
    funext t
    simp only [Pi.mul_apply, div_eq_mul_inv, ← inv_pow]
  have he : IntervalIntegrable (fun t ↦ 2 * (Real.log t / t ^ 2)) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have h :=
      (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (2 : ℝ)) (Set.Icc a b)).mul (hl.mul hc)
    convert h using 1
    funext t
    simp only [Pi.mul_apply, div_eq_mul_inv, ← inv_pow]
  have hz := zeroCount_invSq_integrable ha0 hab
  have hh :=
    intervalIntegral.integral_mono_on hab hz (hm.add he)
      (fun t ht ↦ by
        have h := (abs_le.mp (hQ t ht)).2
        have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
        have hdiv := div_le_div_of_nonneg_right h ht2
        rw [sub_div, mul_div_assoc] at hdiv
        linarith only [hdiv])
  rw [intervalIntegral.integral_add hm he, intervalIntegral.integral_const_mul,
    integral_log_sq ha0 hab] at hh
  exact hh

/-- Under RH, a continuous approximation to the two-sided zero count with
error at most `2 log t` on `[2πe, b]` bounds the inverse-height zero sum.
The upper endpoint error cancels against part of the integrated error. The
zero-count approximation is an explicit hypothesis. -/
theorem reciprocal_sum_of_count_error (hRH : RiemannHypothesis) {b : ℝ} {M : ℝ → ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b) (hM : ContinuousOn M (Set.Icc (2 * Real.pi * Real.exp 1) b))
    (hQ : ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) b, |zeroCount t - M t| ≤ 2 * Real.log t) :
    zeroReciprocalSum b ≤
      M b / b + (∫ t in (2 * Real.pi * Real.exp 1)..b, M t / t ^ 2) +
            2 * ((Real.log (2 * Real.pi * Real.exp 1) + 1) / (2 * Real.pi * Real.exp 1)) -
          2 / b +
        109 / 480 := by
  have h0 : (1 : ℝ) < 2 * Real.pi * Real.exp 1 := by
    have hp :=
      mul_le_mul Real.pi_gt_three.le Real.exp_one_gt_two.le (by norm_num only : (0 : ℝ) ≤ 2)
        Real.pi_pos.le
    nlinarith only [hp]
  have hb0 : 0 < b := lt_of_lt_of_le (zero_lt_one.trans h0) hb
  have hsum := zeroReciprocal_abel_from_cutoff hRH hb
  have hint := count_integral_of_error h0 hb hM hQ
  have hpoint := (abs_le.mp (hQ b ⟨hb, le_rfl⟩)).2
  have hdiv := div_le_div_of_nonneg_right hpoint hb0.le
  rw [sub_div] at hdiv
  have heq : (2 * Real.log b) / b - 2 * ((Real.log b + 1) / b) = -2 / b := by
    simp only [div_eq_mul_inv]
    ring
  simp only [div_eq_mul_inv] at hsum hint hdiv heq ⊢
  nlinarith only [hsum, hint, hdiv, heq]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
