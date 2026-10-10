/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LeftVerticalLogDeriv
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HorizontalFarLeftBound
public import PseudoPrime.AnalyticNumberTheory.General.GeometricDecay

/-!
# Left-vertical contour estimates

On `Re s=-(2m+1)`, the logarithmic derivative has a bound affine in `m`
and `|t|`. Estimate both contour kernels and integrate over `[-T,T]`.
For `x > 1`, geometric decay in `m` absorbs polynomially growing heights,
including the common far-left height sequence.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `x > 0` and any real `t`, bound the logarithmic contour kernel on
`Re s=-(2m+1)`. Its numerator norm is the constant `x^(-(2m+1))` along this line. -/
theorem norm_riemannZetaLogContourKernel_leftVertical_le {x : ℝ} (hx : 0 < x) {m : ℕ} {t : ℝ} :
    ‖riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) ^ 2 := by
  set z : ℂ := -(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzre : z.re = -(2 * (m : ℝ) + 1) := by
    rw [hz_def]
    simp only [neg_add_rev, Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
      Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero,
      sub_zero, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero]
  have hderiv_bound := norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform m t
  have hlogDeriv_eq : ‖deriv riemannZeta z / riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := by
    rw [logDeriv_apply]
  have hxz : ‖(x : ℂ) ^ z‖ = x ^ (-(2 * (m : ℝ) + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hzre]
  have hxσpos : (0 : ℝ) < x ^ (-(2 * (m : ℝ) + 1)) := Real.rpow_pos_of_pos hx _
  have hm1pos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hznorm_ge : 2 * (m : ℝ) + 1 ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    rw [hzre] at h
    rw [abs_neg, abs_of_pos hm1pos] at h
    exact h
  have hznorm_pos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le hm1pos hznorm_ge
  have hK_eq :
    ‖riemannZetaLogContourKernel x z‖ =
      ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 1)) / ‖z‖ ^ 2 := by
    unfold riemannZetaLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hxz, hlogDeriv_eq, norm_pow]
  rw [hK_eq]
  have h1 :
    ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 1)) ≤
      leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right hderiv_bound hxσpos.le
  have h2 : (0 : ℝ) ≤ ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 1)) := by positivity
  have h3 : (2 * (m : ℝ) + 1) ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hm1pos.le hznorm_ge 2
  calc
    ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 1)) / ‖z‖ ^ 2 ≤
        ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) ^ 2 :=
      by apply div_le_div_of_nonneg_left h2 (by positivity) h3
    _ ≤ (leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 1))) / (2 * (m : ℝ) + 1) ^ 2 := by
      apply div_le_div_of_nonneg_right h1 (by positivity)

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZetaLogContourKernel_leftVertical_le`.
Since `PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZetaReciprocalContourKernel` carries
`x ^ (s - 1) / (s * (s - 1))`, the denominator's second
factor uses `‖z - 1‖ ≥ |Re(z) - 1| = 2m + 2`. -/
theorem norm_riemannZetaReciprocalContourKernel_leftVertical_le {x : ℝ} (hx : 0 < x) {m : ℕ}
    {t : ℝ} :
    ‖riemannZetaReciprocalContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 2)) /
        ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) := by
  set z : ℂ := -(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzre : z.re = -(2 * (m : ℝ) + 1) := by
    rw [hz_def]
    simp only [neg_add_rev, Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
      Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero,
      sub_zero, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero]
  have hz1re : (z - 1).re = -(2 * (m : ℝ) + 2) := by
    rw [Complex.sub_re, hzre, Complex.one_re]
    ring
  have hderiv_bound := norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform m t
  have hlogDeriv_eq : ‖deriv riemannZeta z / riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := by
    rw [logDeriv_apply]
  have hxz : ‖(x : ℂ) ^ (z - 1)‖ = x ^ (-(2 * (m : ℝ) + 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hz1re]
  have hxσpos : (0 : ℝ) < x ^ (-(2 * (m : ℝ) + 2)) := Real.rpow_pos_of_pos hx _
  have hm1pos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hm2pos : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
  have hznorm_ge : 2 * (m : ℝ) + 1 ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    rw [hzre, abs_neg, abs_of_pos hm1pos] at h
    exact h
  have hz1norm_ge : 2 * (m : ℝ) + 2 ≤ ‖z - 1‖ := by
    have h := Complex.abs_re_le_norm (z - 1)
    rw [hz1re, abs_neg, abs_of_pos hm2pos] at h
    exact h
  have hK_eq :
    ‖riemannZetaReciprocalContourKernel x z‖ =
      ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 2)) / (‖z‖ * ‖z - 1‖) := by
    unfold riemannZetaReciprocalContourKernel
    rw [norm_div, norm_mul, norm_neg, hxz, hlogDeriv_eq, norm_mul]
  rw [hK_eq]
  have h1 :
    ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 2)) ≤
      leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_right hderiv_bound hxσpos.le
  have h2 : (0 : ℝ) ≤ ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 2)) := by positivity
  have h3 : (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2) ≤ ‖z‖ * ‖z - 1‖ :=
    mul_le_mul hznorm_ge hz1norm_ge hm2pos.le (le_trans hm1pos.le hznorm_ge)
  calc
    ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 2)) / (‖z‖ * ‖z - 1‖) ≤
        ‖logDeriv riemannZeta z‖ * x ^ (-(2 * (m : ℝ) + 2)) /
          ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) :=
      by apply div_le_div_of_nonneg_left h2 (by positivity) h3
    _ ≤
        (leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 2))) /
          ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) :=
      by apply div_le_div_of_nonneg_right h1 (by positivity)

/-- The pointwise kernel bound, integrated over the vertical segment `t ∈ [-T, T]`. -/
theorem norm_intervalIntegral_riemannZetaLogContourKernel_leftVertical_le {x : ℝ} (hx : 0 < x)
    {m : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) ^ 2 *
        (2 * T) := by
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T) (f := fun t : ℝ =>
      riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)) (C :=
      leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) ^ 2)
      (by
        rw [Set.uIoc_of_le (by linarith only [hT] : -T ≤ T)]
        rintro t ⟨ht1, ht2⟩
        have hbase := norm_riemannZetaLogContourKernel_leftVertical_le (x := x) hx (m := m) (t := t)
        have htabs : |t| ≤ T := abs_le.mpr ⟨ht1.le, ht2⟩
        have hle : leftVerticalZetaLogDerivBound m t ≤ leftVerticalZetaLogDerivBound m T := by
          unfold leftVerticalZetaLogDerivBound
          rw [abs_of_nonneg hT]
          nlinarith only [mul_le_mul_of_nonneg_left htabs Real.pi_pos.le]
        calc
          ‖riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 1)) /
                (2 * (m : ℝ) + 1) ^ 2 :=
            hbase
          _ ≤
              leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) /
                (2 * (m : ℝ) + 1) ^ 2 :=
            by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hle (by positivity))
  rwa [show T - -T = 2 * T from by ring, abs_of_nonneg (mul_nonneg (by norm_num only) hT)] at hbound

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`norm_intervalIntegral_riemannZetaLogContourKernel_leftVertical_le`.
-/
theorem norm_intervalIntegral_riemannZetaReciprocalContourKernel_leftVertical_le {x : ℝ}
    (hx : 0 < x) {m : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T,
          riemannZetaReciprocalContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) /
          ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) *
        (2 * T) := by
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T) (f := fun t : ℝ =>
      riemannZetaReciprocalContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)) (C :=
      leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) /
        ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)))
      (by
        rw [Set.uIoc_of_le (by linarith only [hT] : -T ≤ T)]
        rintro t ⟨ht1, ht2⟩
        have hbase :=
          norm_riemannZetaReciprocalContourKernel_leftVertical_le (x := x) hx (m := m) (t := t)
        have htabs : |t| ≤ T := abs_le.mpr ⟨ht1.le, ht2⟩
        have hle : leftVerticalZetaLogDerivBound m t ≤ leftVerticalZetaLogDerivBound m T := by
          unfold leftVerticalZetaLogDerivBound
          rw [abs_of_nonneg hT]
          nlinarith only [mul_le_mul_of_nonneg_left htabs Real.pi_pos.le]
        calc
          ‖riemannZetaReciprocalContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
              leftVerticalZetaLogDerivBound m t * x ^ (-(2 * (m : ℝ) + 2)) /
                ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) :=
            hbase
          _ ≤
              leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) /
                ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) :=
            by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hle (by positivity))
  rwa [show T - -T = 2 * T from by ring, abs_of_nonneg (mul_nonneg (by norm_num only) hT)] at hbound

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
