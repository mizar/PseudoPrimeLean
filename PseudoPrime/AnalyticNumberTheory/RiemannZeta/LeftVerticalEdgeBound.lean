/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LeftVerticalLogDeriv
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HorizontalFarLeftBound
import PseudoPrime.AnalyticNumberTheory.General.GeometricDecay

/-!
# Left-vertical contour estimates

On `Re s=-(2m+1)`, the logarithmic derivative has a bound affine in `m`
and `|t|`. Estimate both contour kernels and integrate over `[-T,T]`.
For `x > 1`, geometric decay in `m` absorbs polynomially growing heights,
including the common far-left height sequence.
-/

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
    rw [Complex.sub_re, hzre, Complex.one_re]; ring
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
        rw [Set.uIoc_of_le (by linarith : -T ≤ T)]
        rintro t ⟨ht1, ht2⟩
        have hbase := norm_riemannZetaLogContourKernel_leftVertical_le (x := x) hx (m := m) (t := t)
        have htabs : |t| ≤ T := abs_le.mpr ⟨ht1.le, ht2⟩
        have hle : leftVerticalZetaLogDerivBound m t ≤ leftVerticalZetaLogDerivBound m T := by
          unfold leftVerticalZetaLogDerivBound
          rw [abs_of_nonneg hT]
          nlinarith [mul_le_mul_of_nonneg_left htabs Real.pi_pos.le]
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
  rwa [show T - -T = 2 * T from by ring, abs_of_nonneg (by linarith)] at hbound

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
        rw [Set.uIoc_of_le (by linarith : -T ≤ T)]
        rintro t ⟨ht1, ht2⟩
        have hbase :=
          norm_riemannZetaReciprocalContourKernel_leftVertical_le (x := x) hx (m := m) (t := t)
        have htabs : |t| ≤ T := abs_le.mpr ⟨ht1.le, ht2⟩
        have hle : leftVerticalZetaLogDerivBound m t ≤ leftVerticalZetaLogDerivBound m T := by
          unfold leftVerticalZetaLogDerivBound
          rw [abs_of_nonneg hT]
          nlinarith [mul_le_mul_of_nonneg_left htabs Real.pi_pos.le]
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
  rwa [show T - -T = 2 * T from by ring, abs_of_nonneg (by linarith)] at hbound

/-- For fixed `x > 1`, the logarithmic-kernel integral on `Re s=-(2m+1)`
with imaginary part in `[-(m+1),m+1]` tends to zero. Geometric decay absorbs
the polynomial majorant. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_leftVertical_atTop {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ t in (-((m : ℝ) + 1))..((m : ℝ) + 1),
          riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  set C : ℝ := qMinusOneLeftVerticalConst with hC_def
  set K1 : ℝ := |C| + 4 * Real.pi + 2 with hK1_def
  have hK1nn : (0 : ℝ) ≤ K1 := by
    rw [hK1_def]; positivity
  have hbound :
    ∀ m : ℕ,
      ‖∫ t in (-((m : ℝ) + 1))..((m : ℝ) + 1),
            riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        2 * K1 * x ^ (-(1 : ℝ)) * (((m : ℝ) + 1) ^ 2 * (x ^ (-(2 : ℝ))) ^ m) := by
    intro m
    have hbase :=
      norm_intervalIntegral_riemannZetaLogContourKernel_leftVertical_le (x := x) (by linarith) (m :=
        m) (T := (m : ℝ) + 1) (by positivity)
    have hxσpos : (0 : ℝ) < x ^ (-(2 * (m : ℝ) + 1)) := Real.rpow_pos_of_pos (by linarith) _
    have hm1pos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    have hlvbound_le : leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) ≤ K1 * ((m : ℝ) + 1) := by
      unfold leftVerticalZetaLogDerivBound
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
      rw [hK1_def]
      have hCm : |C| ≤ |C| * ((m : ℝ) + 1) :=
        le_mul_of_one_le_right (abs_nonneg C) (by linarith [Nat.cast_nonneg (α := ℝ) m])
      nlinarith [le_abs_self C, Nat.cast_nonneg (α := ℝ) m, hCm]
    have hstep1 :
      leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1)) /
            (2 * (m : ℝ) + 1) ^ 2 *
          (2 * ((m : ℝ) + 1)) ≤
        2 * K1 * ((m : ℝ) + 1) ^ 2 * x ^ (-(2 * (m : ℝ) + 1)) := by
      have hden_ge : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hlvnn : (0 : ℝ) ≤ leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) :=
        le_trans (norm_nonneg _)
          (norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform m ((m : ℝ) + 1))
      have hnum_le :
        leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1)) ≤
          K1 * ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hlvbound_le hxσpos.le
      calc
        leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1)) /
                (2 * (m : ℝ) + 1) ^ 2 *
              (2 * ((m : ℝ) + 1)) ≤
            leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1)) / 1 *
              (2 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (mul_nonneg hlvnn hxσpos.le) one_pos hden_ge) (by positivity)
        _ =
            leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1)) *
              (2 * ((m : ℝ) + 1)) :=
          by ring
        _ ≤ (K1 * ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1))) * (2 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hnum_le (by positivity)
        _ = 2 * K1 * ((m : ℝ) + 1) ^ 2 * x ^ (-(2 * (m : ℝ) + 1)) := by ring
    have hxeq : x ^ (-(2 * (m : ℝ) + 1)) = x ^ (-(1 : ℝ)) * (x ^ (-(2 : ℝ))) ^ m := by
      rw [show -(2 * (m : ℝ) + 1) = -(2 : ℝ) * (m : ℝ) + -(1 : ℝ) from by ring,
        Real.rpow_add (by linarith), Real.rpow_mul (by linarith : (0 : ℝ) ≤ x), Real.rpow_natCast]
      ring
    calc
      ‖∫ t in (-((m : ℝ) + 1))..((m : ℝ) + 1),
              riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          leftVerticalZetaLogDerivBound m ((m : ℝ) + 1) * x ^ (-(2 * (m : ℝ) + 1)) /
              (2 * (m : ℝ) + 1) ^ 2 *
            (2 * ((m : ℝ) + 1)) :=
        hbase
      _ ≤ 2 * K1 * ((m : ℝ) + 1) ^ 2 * x ^ (-(2 * (m : ℝ) + 1)) := hstep1
      _ = 2 * K1 * x ^ (-(1 : ℝ)) * (((m : ℝ) + 1) ^ 2 * (x ^ (-(2 : ℝ))) ^ m) := by
        rw [hxeq]; ring
  have hrpos : (0 : ℝ) ≤ x ^ (-(2 : ℝ)) := by positivity
  have hrlt1 : x ^ (-(2 : ℝ)) < 1 := by
    rw [show (-(2 : ℝ)) = -(2 : ℕ) from by norm_num only, Real.rpow_neg (by linarith),
      Real.rpow_natCast]
    rw [inv_lt_one_iff₀]
    right
    nlinarith [hx, sq_nonneg (x - 1)]
  have htend :
    Filter.Tendsto
      (fun m : ℕ => 2 * K1 * x ^ (-(1 : ℝ)) * (((m : ℝ) + 1) ^ 2 * (x ^ (-(2 : ℝ))) ^ m))
      Filter.atTop (nhds 0) := by
    have :=
      (General.tendsto_add_one_sq_mul_pow_of_lt_one hrpos hrlt1).const_mul (2 * K1 * x ^ (-(1 : ℝ)))
    simpa only [Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, inv_pow, mul_zero] using
      this
  exact squeeze_zero_norm hbound htend

/-- For `x > 1`, the logarithmic left-vertical integral tends to zero using
the same `farLeftHeightSeq` as the horizontal segment. Its polynomial growth
is absorbed by geometric decay, and it dominates `m+1`. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_leftVertical_farLeftHeightSeq {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ t in (-(farLeftHeightSeq m))..(farLeftHeightSeq m),
          riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  set C : ℝ := qMinusOneLeftVerticalConst with hC_def
  set K1 : ℝ := |C| + 4 * Real.pi + 2 with hK1_def
  have hK1nn : (0 : ℝ) ≤ K1 := by
    rw [hK1_def]; positivity
  have hbound :
    ∀ m : ℕ,
      ‖∫ t in (-(farLeftHeightSeq m))..(farLeftHeightSeq m),
            riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        2 * K1 * x ^ (-(1 : ℝ)) * (farLeftHeightSeq m ^ 2 * (x ^ (-(2 : ℝ))) ^ m) := by
    intro m
    set T : ℝ := farLeftHeightSeq m with hT_def
    have hT1 : (1 : ℝ) ≤ T := one_le_farLeftHeightSeq m
    have hTm1 : (m : ℝ) + 1 ≤ T := add_one_le_farLeftHeightSeq m
    have hTpos : (0 : ℝ) < T := farLeftHeightSeq_pos m
    have hbase :=
      norm_intervalIntegral_riemannZetaLogContourKernel_leftVertical_le (x := x) (by linarith) (m :=
        m) (T := T) (by positivity)
    have hxσpos : (0 : ℝ) < x ^ (-(2 * (m : ℝ) + 1)) := Real.rpow_pos_of_pos (by linarith) _
    have hm1pos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    have hlvbound_le : leftVerticalZetaLogDerivBound m T ≤ K1 * T := by
      unfold leftVerticalZetaLogDerivBound
      rw [abs_of_nonneg hTpos.le, hK1_def]
      have hCT : |C| ≤ |C| * T := le_mul_of_one_le_right (abs_nonneg C) hT1
      nlinarith [le_abs_self C, hCT, hTm1]
    have hstep1 :
      leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) ^ 2 *
          (2 * T) ≤
        2 * K1 * T ^ 2 * x ^ (-(2 * (m : ℝ) + 1)) := by
      have hden_ge : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hlvnn : (0 : ℝ) ≤ leftVerticalZetaLogDerivBound m T :=
        le_trans (norm_nonneg _) (norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform m T)
      have hnum_le :
        leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) ≤
          K1 * T * x ^ (-(2 * (m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hlvbound_le hxσpos.le
      calc
        leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) ^ 2 *
              (2 * T) ≤
            leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) / 1 * (2 * T) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (mul_nonneg hlvnn hxσpos.le) one_pos hden_ge) (by positivity)
        _ = leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) * (2 * T) := by ring
        _ ≤ (K1 * T * x ^ (-(2 * (m : ℝ) + 1))) * (2 * T) :=
          mul_le_mul_of_nonneg_right hnum_le (by positivity)
        _ = 2 * K1 * T ^ 2 * x ^ (-(2 * (m : ℝ) + 1)) := by ring
    have hxeq : x ^ (-(2 * (m : ℝ) + 1)) = x ^ (-(1 : ℝ)) * (x ^ (-(2 : ℝ))) ^ m := by
      rw [show -(2 * (m : ℝ) + 1) = -(2 : ℝ) * (m : ℝ) + -(1 : ℝ) from by ring,
        Real.rpow_add (by linarith), Real.rpow_mul (by linarith : (0 : ℝ) ≤ x), Real.rpow_natCast]
      ring
    calc
      ‖∫ t in (-T)..T, riemannZetaLogContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 1)) / (2 * (m : ℝ) + 1) ^ 2 *
            (2 * T) :=
        hbase
      _ ≤ 2 * K1 * T ^ 2 * x ^ (-(2 * (m : ℝ) + 1)) := hstep1
      _ = 2 * K1 * x ^ (-(1 : ℝ)) * (T ^ 2 * (x ^ (-(2 : ℝ))) ^ m) := by
        rw [hxeq]; ring
  have hrpos : (0 : ℝ) ≤ x ^ (-(2 : ℝ)) := by positivity
  have hrlt1 : x ^ (-(2 : ℝ)) < 1 := by
    rw [show (-(2 : ℝ)) = -(2 : ℕ) from by norm_num only, Real.rpow_neg (by linarith),
      Real.rpow_natCast]
    rw [inv_lt_one_iff₀]
    right
    nlinarith [hx, sq_nonneg (x - 1)]
  have htend :
    Filter.Tendsto
      (fun m : ℕ => 2 * K1 * x ^ (-(1 : ℝ)) * (farLeftHeightSeq m ^ 2 * (x ^ (-(2 : ℝ))) ^ m))
      Filter.atTop (nhds 0) := by
    have :=
      (tendsto_farLeftHeightSeq_sq_mul_pow_of_lt_one hrpos hrlt1).const_mul
        (2 * K1 * x ^ (-(1 : ℝ)))
    simpa only [Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, inv_pow, mul_zero] using
      this
  exact squeeze_zero_norm hbound htend

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`tendsto_intervalIntegral_riemannZetaLogContourKernel_leftVertical_farLeftHeightSeq`. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_leftVertical_farLeftHeightSeq
    {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ t in (-(farLeftHeightSeq m))..(farLeftHeightSeq m),
          riemannZetaReciprocalContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  set C : ℝ := qMinusOneLeftVerticalConst with hC_def
  set K1 : ℝ := |C| + 4 * Real.pi + 2 with hK1_def
  have hK1nn : (0 : ℝ) ≤ K1 := by
    rw [hK1_def]; positivity
  have hbound :
    ∀ m : ℕ,
      ‖∫ t in (-(farLeftHeightSeq m))..(farLeftHeightSeq m),
            riemannZetaReciprocalContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        2 * K1 * x ^ (-(2 : ℝ)) * (farLeftHeightSeq m ^ 2 * (x ^ (-(2 : ℝ))) ^ m) := by
    intro m
    set T : ℝ := farLeftHeightSeq m with hT_def
    have hT1 : (1 : ℝ) ≤ T := one_le_farLeftHeightSeq m
    have hTm1 : (m : ℝ) + 1 ≤ T := add_one_le_farLeftHeightSeq m
    have hTpos : (0 : ℝ) < T := farLeftHeightSeq_pos m
    have hbase :=
      norm_intervalIntegral_riemannZetaReciprocalContourKernel_leftVertical_le (x := x)
        (by linarith) (m := m) (T := T) (by positivity)
    have hxσpos : (0 : ℝ) < x ^ (-(2 * (m : ℝ) + 2)) := Real.rpow_pos_of_pos (by linarith) _
    have hm1pos : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
    have hm2pos : (0 : ℝ) < 2 * (m : ℝ) + 2 := by positivity
    have hlvbound_le : leftVerticalZetaLogDerivBound m T ≤ K1 * T := by
      unfold leftVerticalZetaLogDerivBound
      rw [abs_of_nonneg hTpos.le, hK1_def]
      have hCT : |C| ≤ |C| * T := le_mul_of_one_le_right (abs_nonneg C) hT1
      nlinarith [le_abs_self C, hCT, hTm1]
    have hden_ge : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hlvnn : (0 : ℝ) ≤ leftVerticalZetaLogDerivBound m T :=
      le_trans (norm_nonneg _) (norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform m T)
    have hnum_le :
      leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) ≤
        K1 * T * x ^ (-(2 * (m : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_right hlvbound_le hxσpos.le
    have hstep1 :
      leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) /
            ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) *
          (2 * T) ≤
        2 * K1 * T ^ 2 * x ^ (-(2 * (m : ℝ) + 2)) :=
      calc
        leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) /
                ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) *
              (2 * T) ≤
            leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) / 1 * (2 * T) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (mul_nonneg hlvnn hxσpos.le) one_pos hden_ge) (by positivity)
        _ = leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) * (2 * T) := by ring
        _ ≤ (K1 * T * x ^ (-(2 * (m : ℝ) + 2))) * (2 * T) :=
          mul_le_mul_of_nonneg_right hnum_le (by positivity)
        _ = 2 * K1 * T ^ 2 * x ^ (-(2 * (m : ℝ) + 2)) := by ring
    have hxeq : x ^ (-(2 * (m : ℝ) + 2)) = x ^ (-(2 : ℝ)) * (x ^ (-(2 : ℝ))) ^ m := by
      rw [show -(2 * (m : ℝ) + 2) = -(2 : ℝ) * (m : ℝ) + -(2 : ℝ) from by ring,
        Real.rpow_add (by linarith), Real.rpow_mul (by linarith : (0 : ℝ) ≤ x), Real.rpow_natCast]
      ring
    calc
      ‖∫ t in (-T)..T,
              riemannZetaReciprocalContourKernel x (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          leftVerticalZetaLogDerivBound m T * x ^ (-(2 * (m : ℝ) + 2)) /
              ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) *
            (2 * T) :=
        hbase
      _ ≤ 2 * K1 * T ^ 2 * x ^ (-(2 * (m : ℝ) + 2)) := hstep1
      _ = 2 * K1 * x ^ (-(2 : ℝ)) * (T ^ 2 * (x ^ (-(2 : ℝ))) ^ m) := by
        rw [hxeq]; ring
  have hrpos : (0 : ℝ) ≤ x ^ (-(2 : ℝ)) := by positivity
  have hrlt1 : x ^ (-(2 : ℝ)) < 1 := by
    rw [show (-(2 : ℝ)) = -(2 : ℕ) from by norm_num only, Real.rpow_neg (by linarith),
      Real.rpow_natCast]
    rw [inv_lt_one_iff₀]
    right
    nlinarith [hx, sq_nonneg (x - 1)]
  have htend :
    Filter.Tendsto
      (fun m : ℕ => 2 * K1 * x ^ (-(2 : ℝ)) * (farLeftHeightSeq m ^ 2 * (x ^ (-(2 : ℝ))) ^ m))
      Filter.atTop (nhds 0) := by
    have :=
      (tendsto_farLeftHeightSeq_sq_mul_pow_of_lt_one hrpos hrlt1).const_mul
        (2 * K1 * x ^ (-(2 : ℝ)))
    simpa only [Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, inv_pow, mul_zero] using
      this
  exact squeeze_zero_norm hbound htend

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
