/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds
import PseudoPrime.Analysis.IntegralLimits
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SmoothedContour

/-!
# Vertical integrability and truncation limits

For positive `x` and `τ > 1`, both zeta contour kernels are integrable on
`Re s = τ`. Absolute convergence of the von Mangoldt series bounds `ζ'/ζ`,
and the quadratic denominators give integrable decay. The integrals truncated
to `[-T,T]` consequently converge to the full vertical integrals.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-!
The right-half-plane estimate for `‖ζ'/ζ‖` follows from its absolutely
convergent von Mangoldt Dirichlet series.
-/

/-- The logarithmic contour kernel is continuous along any vertical line with `Re s = τ > 1`. -/
theorem continuous_riemannZetaLogContourKernel_line {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    Continuous
      (fun y : ℝ ↦
        riemannZetaLogContourKernel x
          ((τ : ℂ) + y * Complex.I)) := by
  have hOn :
    ContinuousOn (riemannZetaLogContourKernel x)
      {s : ℂ | 1 < s.re} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs
    have hs0 : s ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hs; linarith
    have hszeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    exact
      ContinuousAt.continuousWithinAt
        (differentiableAt_riemannZetaLogContourKernel
            hx hs0 hs1 hszeta).continuousAt
  have hg : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) := by fun_prop
  exact
    hOn.comp_continuous hg
      (fun y ↦ by
        simpa only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using hτ)

/-- The reciprocal contour kernel is continuous along any vertical line with `Re s = τ > 1`. -/
theorem continuous_riemannZetaReciprocalContourKernel_line {x : ℝ} (hx : 0 < x) {τ : ℝ}
    (hτ : 1 < τ) :
    Continuous
      (fun y : ℝ ↦
        riemannZetaReciprocalContourKernel x
          ((τ : ℂ) + y * Complex.I)) := by
  have hOn :
    ContinuousOn (riemannZetaReciprocalContourKernel x)
      {s : ℂ | 1 < s.re} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs
    have hs0 : s ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hs; linarith
    have hszeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    exact
      ContinuousAt.continuousWithinAt
        (differentiableAt_riemannZetaReciprocalContourKernel
            hx hs0 hs1 hszeta).continuousAt
  have hg : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) := by fun_prop
  exact
    hOn.comp_continuous hg
      (fun y ↦ by
        simpa only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using hτ)

/-- The logarithmic contour kernel is integrable along any vertical line with `Re s = τ > 1`,
with no growth theory beyond absolute convergence of the von Mangoldt Dirichlet series. -/
theorem integrable_riemannZetaLogContourKernel {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦
        riemannZetaLogContourKernel x
          ((τ : ℂ) + y * Complex.I)) := by
  set C : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ with hC_def
  have hxτ : (0 : ℝ) < x ^ τ := Real.rpow_pos_of_pos hx τ
  have hτ0 : τ ≠ 0 := by linarith
  apply
    MeasureTheory.Integrable.mono'
      (((General.verticalIntegrable_mellinLogKernel
              hτ0).norm).const_mul
        (C * x ^ τ))
  · exact
      (continuous_riemannZetaLogContourKernel_line hx
          hτ).aestronglyMeasurable
  · filter_upwards with y
    set s : ℂ := (τ : ℂ) + y * Complex.I with hs_def
    have hAle : ‖deriv riemannZeta s / riemannZeta s‖ ≤ C :=
      norm_deriv_riemannZeta_div_le hτ y
    have hBnorm : ‖(x : ℂ) ^ s‖ = x ^ τ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      rw [hs_def]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have hKnorm : ‖s⁻¹ ^ 2‖ = (‖s‖ ^ 2)⁻¹ := by rw [norm_pow, norm_inv, inv_pow]
    change
      ‖riemannZetaLogContourKernel x s‖ ≤
        C * x ^ τ * ‖s⁻¹ ^ 2‖
    unfold riemannZetaLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hBnorm, norm_pow, div_eq_mul_inv, hKnorm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAle hxτ.le) (by positivity)

/-- The reciprocal contour kernel is integrable along any vertical line with `Re s = τ > 1`,
with no growth theory beyond absolute convergence of the von Mangoldt Dirichlet series. -/
theorem integrable_riemannZetaReciprocalContourKernel {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦
        riemannZetaReciprocalContourKernel x
          ((τ : ℂ) + y * Complex.I)) := by
  set C : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ with hC_def
  set σ : ℝ := τ - 1 with hσ_def
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hσ0 : σ ≠ 0 := by
    rw [hσ_def]; intro h; linarith [sub_eq_zero.mp h]
  have hσ1 : σ ≠ -1 := by
    rw [hσ_def]; intro h; linarith
  apply
    MeasureTheory.Integrable.mono'
      (((General.verticalIntegrable_mellinReciprocalKernel hσ0
              hσ1).norm).const_mul
        (C * x ^ σ))
  · exact
      (continuous_riemannZetaReciprocalContourKernel_line
          hx hτ).aestronglyMeasurable
  · filter_upwards with y
    set s : ℂ := (τ : ℂ) + y * Complex.I with hs_def
    set s' : ℂ := (σ : ℂ) + y * Complex.I with hs'_def
    have hAle : ‖deriv riemannZeta s / riemannZeta s‖ ≤ C :=
      norm_deriv_riemannZeta_div_le hτ y
    have hBnorm : ‖(x : ℂ) ^ (s - 1)‖ = x ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      rw [hs_def, hσ_def]
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re]
    have hDenomEq : s * (s - 1) = s' * (s' + 1) := by
      rw [hs_def, hs'_def, hσ_def]; push_cast; ring
    change
      ‖riemannZetaReciprocalContourKernel x s‖ ≤
        C * x ^ σ * ‖(s' * (s' + 1))⁻¹‖
    unfold riemannZetaReciprocalContourKernel
    rw [norm_div, norm_mul, norm_neg, hBnorm, div_eq_mul_inv, ← hDenomEq, ← norm_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAle hxσ.le) (norm_nonneg _)

/-!
### Truncated vertical integrals converge to the full line

Integrability on `Re s = τ > 1` allows application of
`intervalIntegral_tendsto_integral` as `T` tends to infinity.
-/

theorem tendsto_intervalIntegral_riemannZetaLogContourKernel {x : ℝ} (hx : 0 < x) {τ : ℝ}
    (hτ : 1 < τ) :
    Filter.Tendsto
      (fun T : ℝ ↦
        ∫ y in (-T)..T,
          riemannZetaLogContourKernel x
            ((τ : ℂ) + y * Complex.I))
      Filter.atTop
      (nhds
        (∫ y : ℝ,
          riemannZetaLogContourKernel x
            ((τ : ℂ) + y * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_riemannZetaLogContourKernel hx hτ)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.tendsto_intervalIntegral_riemannZetaLogContourKernel`.
-/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel {x : ℝ} (hx : 0 < x) {τ : ℝ}
    (hτ : 1 < τ) :
    Filter.Tendsto
      (fun T : ℝ ↦
        ∫ y in (-T)..T,
          riemannZetaReciprocalContourKernel x
            ((τ : ℂ) + y * Complex.I))
      Filter.atTop
      (nhds
        (∫ y : ℝ,
          riemannZetaReciprocalContourKernel x
            ((τ : ℂ) + y * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_riemannZetaReciprocalContourKernel hx
      hτ)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
