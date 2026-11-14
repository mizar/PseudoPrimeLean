/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountInverseSquare

/-! # Abel summation with a general zero-count error -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A continuous error budget for a continuous zero-count approximation bounds
its inverse-square integral on any positive interval. This general form keeps
all terms of a sharp zero-count estimate for subsequent Abel summation. -/
theorem count_integral_le_of_error {a b : ℝ} {M E : ℝ → ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hM : ContinuousOn M (Set.Icc a b)) (hE : ContinuousOn E (Set.Icc a b))
    (hQ : ∀ t ∈ Set.Icc a b, |zeroCount t - M t| ≤ E t) :
    (∫ t in a..b, zeroCount t / t ^ 2) ≤
      (∫ t in a..b, M t / t ^ 2) + (∫ t in a..b, E t / t ^ 2) := by
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.Icc a b) := by
    intro t ht
    exact ((continuousAt_id.inv₀ (ne_of_gt (lt_of_lt_of_le ha ht.1))).pow 2).continuousWithinAt
  have hm : IntervalIntegrable (fun t ↦ M t / t ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have h := hM.mul hc
    convert h using 1
    funext t
    simp only [Pi.mul_apply, div_eq_mul_inv, ← inv_pow]
  have he : IntervalIntegrable (fun t ↦ E t / t ^ 2) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    have h := hE.mul hc
    convert h using 1
    funext t
    simp only [Pi.mul_apply, div_eq_mul_inv, ← inv_pow]
  have hz := zeroCount_invSq_integrable ha hab
  have hh :=
    intervalIntegral.integral_mono_on hab hz (hm.add he)
      (fun t ht ↦ by
        have h := (abs_le.mp (hQ t ht)).2
        have hdiv := div_le_div_of_nonneg_right h (sq_nonneg t)
        rw [sub_div] at hdiv
        linarith only [hdiv])
  rw [intervalIntegral.integral_add hm he] at hh
  exact hh

/-- For `1 < a ≤ b`, a continuous zero-count approximation and error budget
bound the reciprocal sum between the two heights. The lower endpoint count is
retained, which allows a certified finite zero count to sharpen the estimate. -/
theorem reciprocal_interval_le_of_error {a b : ℝ} {M E : ℝ → ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hM : ContinuousOn M (Set.Icc a b)) (hE : ContinuousOn E (Set.Icc a b))
    (hQ : ∀ t ∈ Set.Icc a b, |zeroCount t - M t| ≤ E t) :
    zeroReciprocalSum b - zeroReciprocalSum a ≤
      M b / b - zeroCount a / a + (∫ t in a..b, M t / t ^ 2) + E b / b +
        (∫ t in a..b, E t / t ^ 2) := by
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hsum := zeroReciprocal_abel ha hab
  have hint := count_integral_le_of_error ha0 hab hM hE hQ
  have hpoint := (abs_le.mp (hQ b ⟨hab, le_rfl⟩)).2
  have hdiv := div_le_div_of_nonneg_right hpoint hb0.le
  rw [sub_div] at hdiv
  linarith only [hsum, hint, hdiv]

/-- Under RH, any continuous approximation and error budget valid from `2πe`
to `b` bound the reciprocal zero sum. The explicit endpoint and integral budget
terms remain separate so that sharp coefficients can be retained. -/
theorem reciprocal_sum_le_of_error (hRH : RiemannHypothesis) {b : ℝ} {M E : ℝ → ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b) (hM : ContinuousOn M (Set.Icc (2 * Real.pi * Real.exp 1) b))
    (hE : ContinuousOn E (Set.Icc (2 * Real.pi * Real.exp 1) b))
    (hQ : ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) b, |zeroCount t - M t| ≤ E t) :
    zeroReciprocalSum b ≤
      M b / b + (∫ t in (2 * Real.pi * Real.exp 1)..b, M t / t ^ 2) +
        (E b / b + (∫ t in (2 * Real.pi * Real.exp 1)..b, E t / t ^ 2)) +
        109 / 480 := by
  have ha : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have hb0 : 0 < b := ha.trans_le hb
  have hsum := zeroReciprocal_abel_from_cutoff hRH hb
  have hint := count_integral_le_of_error ha hb hM hE hQ
  have hpoint := (abs_le.mp (hQ b ⟨hb, le_rfl⟩)).2
  have hdiv := div_le_div_of_nonneg_right hpoint hb0.le
  rw [sub_div] at hdiv
  linarith only [hsum, hint, hdiv]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
