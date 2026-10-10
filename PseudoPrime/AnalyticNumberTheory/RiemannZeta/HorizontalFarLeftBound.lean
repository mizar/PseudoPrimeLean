/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FarLeftLogDeriv
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SmoothedContour
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.GrowthElementary
public import PseudoPrime.AnalyticNumberTheory.General.GeometricDecay

/-!
# Far-left horizontal contour estimates

Combine the logarithmic-derivative majorant on `[-(2m+1),-1/2]+it` with the
power and denominator bounds for both kernels. For `x > 1`, integration and
the chosen growing height sequence make these horizontal integrals vanish.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `x > 1` and `t ≠ 0`, bound the logarithmic kernel on
`σ ∈ [-(2m+1),-1/2]`. The numerator satisfies `x^σ ≤ x^(-1/2)` and the
denominator is at least `t²`; the remaining majorant bounds `‖ζ'/ζ‖`. -/
theorem norm_riemannZetaLogContourKernel_farLeft_le {x : ℝ} (hx : 1 < x) {m : ℕ} {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (-(2 * (m : ℝ) + 1)) (-1 / 2)) (ht : t ≠ 0) :
    ‖riemannZetaLogContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      farLeftZetaLogDerivBound m t * x ^ (-(1 : ℝ) / 2) / t ^ 2 := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzim : z.im = t := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hderiv_bound := norm_logDeriv_riemannZeta_neg_add_mul_I_le_of_mem_Icc hσ ht
  have hlogDeriv_eq : ‖deriv riemannZeta z / riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := by
    rw [logDeriv_apply]
  have hxpos : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have hxz : ‖(x : ℂ) ^ z‖ = x ^ σ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hzre]
  have hxσpos : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hxpos σ
  have hxσ_le : x ^ σ ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hx.le hσ.2
  have htnz : t ≠ 0 := ht
  have hznorm_ge : |t| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rwa [hzim] at h
  have htabs_pos : (0 : ℝ) < |t| := abs_pos.mpr htnz
  have hznorm_pos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le htabs_pos hznorm_ge
  have hK_eq : ‖riemannZetaLogContourKernel x z‖ = ‖logDeriv riemannZeta z‖ * x ^ σ / ‖z‖ ^ 2 := by
    unfold riemannZetaLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hxz, hlogDeriv_eq, norm_pow]
  rw [hK_eq]
  have h1 : ‖logDeriv riemannZeta z‖ * x ^ σ ≤ farLeftZetaLogDerivBound m t * x ^ (-(1 : ℝ) / 2) :=
    mul_le_mul hderiv_bound hxσ_le hxσpos.le (le_trans (norm_nonneg _) hderiv_bound)
  have h2 : (0 : ℝ) ≤ ‖logDeriv riemannZeta z‖ * x ^ σ := by positivity
  have h3 : t ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs t]
    exact pow_le_pow_left₀ (abs_nonneg t) hznorm_ge 2
  have htsq_pos : (0 : ℝ) < t ^ 2 := by positivity
  calc
    ‖logDeriv riemannZeta z‖ * x ^ σ / ‖z‖ ^ 2 ≤ ‖logDeriv riemannZeta z‖ * x ^ σ / t ^ 2 := by
      apply div_le_div_of_nonneg_left h2 htsq_pos h3
    _ ≤ (farLeftZetaLogDerivBound m t * x ^ (-(1 : ℝ) / 2)) / t ^ 2 := by
      apply div_le_div_of_nonneg_right h1 htsq_pos.le

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZetaLogContourKernel_farLeft_le`. Since
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZetaReciprocalContourKernel` carries
`x ^ (s - 1) / (s * (s - 1))`, the exponent shifts to
`σ - 1 ≤ -3/2`, still bounded (for `x > 1`) by the fixed value `x ^ (-3/2)`. -/
theorem norm_riemannZetaReciprocalContourKernel_farLeft_le {x : ℝ} (hx : 1 < x) {m : ℕ} {σ t : ℝ}
    (hσ : σ ∈ Set.Icc (-(2 * (m : ℝ) + 1)) (-1 / 2)) (ht : t ≠ 0) :
    ‖riemannZetaReciprocalContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      farLeftZetaLogDerivBound m t * x ^ (-(3 : ℝ) / 2) / t ^ 2 := by
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzim : z.im = t := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hz1im : (z - 1).im = t := by
    simp only [hz_def, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      Complex.one_im, sub_zero]
  have hderiv_bound := norm_logDeriv_riemannZeta_neg_add_mul_I_le_of_mem_Icc hσ ht
  have hlogDeriv_eq : ‖deriv riemannZeta z / riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := by
    rw [logDeriv_apply]
  have hxpos : (0 : ℝ) < x := by linarith only [hx]
  have hxz : ‖(x : ℂ) ^ (z - 1)‖ = x ^ (σ - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, Complex.sub_re, hzre, Complex.one_re]
  have hxσpos : (0 : ℝ) < x ^ (σ - 1) := Real.rpow_pos_of_pos hxpos (σ - 1)
  have hxσ_le : x ^ (σ - 1) ≤ x ^ (-(3 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hσ.2])
  have htnz : t ≠ 0 := ht
  have htabs_pos : (0 : ℝ) < |t| := abs_pos.mpr htnz
  have hznorm_ge : |t| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rwa [hzim] at h
  have hz1norm_ge : |t| ≤ ‖z - 1‖ := by
    have h := Complex.abs_im_le_norm (z - 1)
    rwa [hz1im] at h
  have hK_eq :
    ‖riemannZetaReciprocalContourKernel x z‖ =
      ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) / (‖z‖ * ‖z - 1‖) := by
    unfold riemannZetaReciprocalContourKernel
    rw [norm_div, norm_mul, norm_neg, hxz, hlogDeriv_eq, norm_mul]
  rw [hK_eq]
  have h1 :
    ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) ≤ farLeftZetaLogDerivBound m t * x ^ (-(3 : ℝ) / 2) :=
    mul_le_mul hderiv_bound hxσ_le hxσpos.le (le_trans (norm_nonneg _) hderiv_bound)
  have h2 : (0 : ℝ) ≤ ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) := by positivity
  have h3 : t ^ 2 ≤ ‖z‖ * ‖z - 1‖ := by
    calc
      t ^ 2 = |t| * |t| := by rw [← sq_abs t, sq]
      _ ≤ ‖z‖ * ‖z - 1‖ :=
        mul_le_mul hznorm_ge hz1norm_ge htabs_pos.le (le_trans htabs_pos.le hznorm_ge)
  have htsq_pos : (0 : ℝ) < t ^ 2 := by positivity
  calc
    ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) / (‖z‖ * ‖z - 1‖) ≤
        ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) / t ^ 2 :=
      by apply div_le_div_of_nonneg_left h2 htsq_pos h3
    _ ≤ (farLeftZetaLogDerivBound m t * x ^ (-(3 : ℝ) / 2)) / t ^ 2 := by
      apply div_le_div_of_nonneg_right h1 htsq_pos.le

/-- The pointwise kernel bound, integrated over the full far-left segment `[-(2m+1), -1/2]` at a
fixed height `t ≠ 0`. -/
theorem norm_intervalIntegral_riemannZetaLogContourKernel_farLeft_le {x : ℝ} (hx : 1 < x) {m : ℕ}
    {t : ℝ} (ht : t ≠ 0) :
    ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaLogContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      farLeftZetaLogDerivBound m t * x ^ (-(1 : ℝ) / 2) / t ^ 2 *
        (-1 / 2 - (-(2 * (m : ℝ) + 1))) := by
  have hlamtau : (-(2 * (m : ℝ) + 1)) ≤ -1 / 2 := by
    have hm := Nat.cast_nonneg (α := ℝ) m
    linarith only [hm]
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := -(2 * (m : ℝ) + 1)) (b := -1 / 2) (f :=
      fun σ : ℝ => riemannZetaLogContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) (C :=
      farLeftZetaLogDerivBound m t * x ^ (-(1 : ℝ) / 2) / t ^ 2)
      (by
        rw [Set.uIoc_of_le hlamtau]
        rintro σ ⟨hσ1, hσ2⟩
        exact norm_riemannZetaLogContourKernel_farLeft_le hx ⟨hσ1.le, hσ2⟩ ht)
  rwa [abs_of_nonneg (by linarith only [hlamtau] : (0 : ℝ) ≤ -1 / 2 - (-(2 * (m : ℝ) + 1)))] at
    hbound

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`norm_intervalIntegral_riemannZetaLogContourKernel_farLeft_le`. -/
theorem norm_intervalIntegral_riemannZetaReciprocalContourKernel_farLeft_le {x : ℝ} (hx : 1 < x)
    {m : ℕ} {t : ℝ} (ht : t ≠ 0) :
    ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaReciprocalContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      farLeftZetaLogDerivBound m t * x ^ (-(3 : ℝ) / 2) / t ^ 2 *
        (-1 / 2 - (-(2 * (m : ℝ) + 1))) := by
  have hlamtau : (-(2 * (m : ℝ) + 1)) ≤ -1 / 2 := by
    have hm := Nat.cast_nonneg (α := ℝ) m
    linarith only [hm]
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := -(2 * (m : ℝ) + 1)) (b := -1 / 2) (f :=
      fun σ : ℝ => riemannZetaReciprocalContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) (C :=
      farLeftZetaLogDerivBound m t * x ^ (-(3 : ℝ) / 2) / t ^ 2)
      (by
        rw [Set.uIoc_of_le hlamtau]
        rintro σ ⟨hσ1, hσ2⟩
        exact norm_riemannZetaReciprocalContourKernel_farLeft_le hx ⟨hσ1.le, hσ2⟩ ht)
  rwa [abs_of_nonneg (by linarith only [hlamtau] : (0 : ℝ) ≤ -1 / 2 - (-(2 * (m : ℝ) + 1)))] at
    hbound

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
