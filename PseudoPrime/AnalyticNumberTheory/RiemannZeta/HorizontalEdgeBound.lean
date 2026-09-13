/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HeightSequence
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ContourLimit
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound

/-!
# Horizontal kernel bounds at good heights

For positive `x`, the good-height bound on `ζ'/ζ` and the two kernels'
denominators give `O(log(T+2)²/T²)` bounds on `[-1/2,2]+iT`.
Integrating over a fixed subsegment gives corresponding integral bounds and
convergence to zero along the good-height sequence.
-/

noncomputable section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At a good height `T`, the logarithmic contour kernel's norm on the horizontal line
`Im s = T` is bounded by an explicit `O((log(T+2))² / T²)` expression, uniformly for
`Re s = σ ∈ [-1/2, 2]`. The `x`-dependence is absorbed into the fixed factor
`max (x ^ (-1/2)) (x ^ 2)`, which dominates `x ^ σ` for every `σ` in this range regardless of
whether `x ≤ 1` or `x ≥ 1`. -/
theorem norm_riemannZetaLogContourKernel_good_height_le {x : ℝ} (hx : 0 < x) {H : ℝ} (hH : 8 ≤ H)
    {T : ℝ} (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    {σ : ℝ} (hσ1 : -(1 : ℝ) / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖riemannZetaLogContourKernel x
          (σ + T * Complex.I)‖ ≤
      qMinusOneZetaLogDerivConst *
          Real.log (T + 2) ^ 2 *
          max (x ^ (-(1 : ℝ) / 2)) (x ^ (2 : ℝ)) /
        T ^ 2 := by
  set z : ℂ := σ + T * Complex.I with hz_def
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hTpos : (0 : ℝ) < T := by linarith [hT.1]
  have hzgood : riemannZeta z ≠ 0 :=
    riemannZeta_ne_zero_of_good_height hH hT hgood σ
  have hderiv_bound :=
    forall_norm_logDeriv_riemannZeta_le hH hT hgood σ
      hσ1 hσ2 hzgood
  have hlogDeriv_eq : ‖deriv riemannZeta z / riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := by
    rw [logDeriv_apply]
  have hxz : ‖(x : ℂ) ^ z‖ = x ^ σ := by rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hzre]
  have hxσpos : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hxσ_le : x ^ σ ≤ max (x ^ (-(1 : ℝ) / 2)) (x ^ (2 : ℝ)) := by
    rcases le_total x 1 with hx1 | hx1
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith))
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hx1 hσ2)
  have hznorm_ge : T ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hzim, abs_of_nonneg hTpos.le] at h
    exact h
  have hznorm_pos : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le hTpos hznorm_ge
  have hK_eq :
    ‖riemannZetaLogContourKernel x z‖ =
      ‖logDeriv riemannZeta z‖ * x ^ σ / ‖z‖ ^ 2 := by
    unfold riemannZetaLogContourKernel
    rw [norm_div, norm_mul, norm_neg, hxz, hlogDeriv_eq, norm_pow]
  rw [hK_eq]
  have h1 :
    ‖logDeriv riemannZeta z‖ * x ^ σ ≤
      qMinusOneZetaLogDerivConst *
        Real.log (T + 2) ^ 2 *
        max (x ^ (-(1 : ℝ) / 2)) (x ^ (2 : ℝ)) :=
    mul_le_mul hderiv_bound hxσ_le hxσpos.le
      (mul_nonneg qMinusOneZetaLogDerivConst_nonneg
        (by positivity))
  have h2 : (0 : ℝ) ≤ ‖logDeriv riemannZeta z‖ * x ^ σ := by positivity
  have h3 : T ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hTpos.le hznorm_ge 2
  calc
    ‖logDeriv riemannZeta z‖ * x ^ σ / ‖z‖ ^ 2 ≤ ‖logDeriv riemannZeta z‖ * x ^ σ / T ^ 2 := by
      apply div_le_div_of_nonneg_left h2 (by positivity) h3
    _ ≤
        (qMinusOneZetaLogDerivConst *
            Real.log (T + 2) ^ 2 *
            max (x ^ (-(1 : ℝ) / 2)) (x ^ (2 : ℝ))) /
          T ^ 2 :=
      by apply div_le_div_of_nonneg_right h1 (by positivity)

/-- The reciprocal-kernel analogue of
`RiemannZeta.norm_riemannZetaLogContourKernel_good_height_le`. Since
`RiemannZeta.riemannZetaReciprocalContourKernel` carries `x ^ (s - 1) / (s * (s - 1))` instead of
`x ^ s / s ^ 2`, the exponent range shifts to `σ - 1 ∈ [-3/2, 1]` and the denominator's lower
bound comes from `‖z‖ ≥ T` and `‖z - 1‖ ≥ T` separately (both via the imaginary-part projection,
since `Im(z - 1) = Im z = T`). -/
theorem norm_riemannZetaReciprocalContourKernel_good_height_le {x : ℝ} (hx : 0 < x) {H : ℝ}
    (hH : 8 ≤ H) {T : ℝ} (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    {σ : ℝ} (hσ1 : -(1 : ℝ) / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖riemannZetaReciprocalContourKernel x
          (σ + T * Complex.I)‖ ≤
      qMinusOneZetaLogDerivConst *
          Real.log (T + 2) ^ 2 *
          max (x ^ (-(3 : ℝ) / 2)) (x ^ (1 : ℝ)) /
        T ^ 2 := by
  set z : ℂ := σ + T * Complex.I with hz_def
  have hzim : z.im = T := by
    simp only [hz_def, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hzre : z.re = σ := by
    simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hz1im : (z - 1).im = T := by
    simp only [hz_def, Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      Complex.one_im, sub_zero]
  have hTpos : (0 : ℝ) < T := by linarith [hT.1]
  have hzgood : riemannZeta z ≠ 0 :=
    riemannZeta_ne_zero_of_good_height hH hT hgood σ
  have hderiv_bound :=
    forall_norm_logDeriv_riemannZeta_le hH hT hgood σ
      hσ1 hσ2 hzgood
  have hlogDeriv_eq : ‖deriv riemannZeta z / riemannZeta z‖ = ‖logDeriv riemannZeta z‖ := by
    rw [logDeriv_apply]
  have hxz : ‖(x : ℂ) ^ (z - 1)‖ = x ^ (σ - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, hzre, Complex.one_re]
  have hxσpos : (0 : ℝ) < x ^ (σ - 1) := Real.rpow_pos_of_pos hx (σ - 1)
  have hxσ_le : x ^ (σ - 1) ≤ max (x ^ (-(3 : ℝ) / 2)) (x ^ (1 : ℝ)) := by
    rcases le_total x 1 with hx1 | hx1
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith))
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  have hznorm_ge : T ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    rw [hzim, abs_of_nonneg hTpos.le] at h
    exact h
  have hz1norm_ge : T ≤ ‖z - 1‖ := by
    have h := Complex.abs_im_le_norm (z - 1)
    rw [hz1im, abs_of_nonneg hTpos.le] at h
    exact h
  have hK_eq :
    ‖riemannZetaReciprocalContourKernel x z‖ =
      ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) / (‖z‖ * ‖z - 1‖) := by
    unfold riemannZetaReciprocalContourKernel
    rw [norm_div, norm_mul, norm_neg, hxz, hlogDeriv_eq, norm_mul]
  rw [hK_eq]
  have h1 :
    ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) ≤
      qMinusOneZetaLogDerivConst *
        Real.log (T + 2) ^ 2 *
        max (x ^ (-(3 : ℝ) / 2)) (x ^ (1 : ℝ)) :=
    mul_le_mul hderiv_bound hxσ_le hxσpos.le
      (mul_nonneg qMinusOneZetaLogDerivConst_nonneg
        (by positivity))
  have h2 : (0 : ℝ) ≤ ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) := by positivity
  have h3 : T ^ 2 ≤ ‖z‖ * ‖z - 1‖ := by
    calc
      T ^ 2 = T * T := sq T
      _ ≤ ‖z‖ * ‖z - 1‖ := mul_le_mul hznorm_ge hz1norm_ge hTpos.le (le_trans hTpos.le hznorm_ge)
  calc
    ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) / (‖z‖ * ‖z - 1‖) ≤
        ‖logDeriv riemannZeta z‖ * x ^ (σ - 1) / T ^ 2 :=
      by apply div_le_div_of_nonneg_left h2 (by positivity) h3
    _ ≤
        (qMinusOneZetaLogDerivConst *
            Real.log (T + 2) ^ 2 *
            max (x ^ (-(3 : ℝ) / 2)) (x ^ (1 : ℝ))) /
          T ^ 2 :=
      by apply div_le_div_of_nonneg_right h1 (by positivity)

/-- Integrate the pointwise logarithmic-kernel bound over a fixed segment
`[lam,tau] ⊆ [-1/2,2]` at a good height. -/
theorem norm_intervalIntegral_riemannZetaLogContourKernel_good_height_le {x : ℝ} (hx : 0 < x)
    {H : ℝ} (hH : 8 ≤ H) {T : ℝ} (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    ‖∫ σ in lam..tau,
          riemannZetaLogContourKernel x
            (σ + T * Complex.I)‖ ≤
      qMinusOneZetaLogDerivConst *
            Real.log (T + 2) ^ 2 *
            max (x ^ (-(1 : ℝ) / 2)) (x ^ (2 : ℝ)) /
          T ^ 2 *
        (tau - lam) := by
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := lam) (b := tau) (f := fun σ : ℝ =>
      riemannZetaLogContourKernel x
        (σ + T * Complex.I))
      (C :=
      qMinusOneZetaLogDerivConst *
          Real.log (T + 2) ^ 2 *
          max (x ^ (-(1 : ℝ) / 2)) (x ^ (2 : ℝ)) /
        T ^ 2)
      (by
        rw [Set.uIoc_of_le hlamtau]
        rintro σ ⟨hσ1, hσ2⟩
        exact
          norm_riemannZetaLogContourKernel_good_height_le
            hx hH hT hgood (le_trans hlam hσ1.le) (hσ2.trans htau))
  rwa [abs_of_nonneg (by linarith only [hlamtau] : (0 : ℝ) ≤ tau - lam)] at hbound

/-- The reciprocal-kernel analogue of
`RiemannZeta.norm_intervalIntegral_riemannZetaLogContourKernel_good_height_le`. -/
theorem norm_intervalIntegral_riemannZetaReciprocalContourKernel_good_height_le {x : ℝ} (hx : 0 < x)
    {H : ℝ} (hH : 8 ≤ H) {T : ℝ} (hT : T ∈ Set.Icc H (H + 1))
    (hgood :
      ∀ ρ : ℂ,
        riemannZeta ρ = 0 →
          |ρ.im - H| ≤ 2 →
          1 / (4 * jensenLogConst * Real.log (H + 2)) ≤
            |T - ρ.im|)
    {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    ‖∫ σ in lam..tau,
          riemannZetaReciprocalContourKernel x
            (σ + T * Complex.I)‖ ≤
      qMinusOneZetaLogDerivConst *
            Real.log (T + 2) ^ 2 *
            max (x ^ (-(3 : ℝ) / 2)) (x ^ (1 : ℝ)) /
          T ^ 2 *
        (tau - lam) := by
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := lam) (b := tau) (f := fun σ : ℝ =>
      riemannZetaReciprocalContourKernel x
        (σ + T * Complex.I))
      (C :=
      qMinusOneZetaLogDerivConst *
          Real.log (T + 2) ^ 2 *
          max (x ^ (-(3 : ℝ) / 2)) (x ^ (1 : ℝ)) /
        T ^ 2)
      (by
        rw [Set.uIoc_of_le hlamtau]
        rintro σ ⟨hσ1, hσ2⟩
        exact
          norm_riemannZetaReciprocalContourKernel_good_height_le
            hx hH hT hgood (le_trans hlam hσ1.le) (hσ2.trans htau))
  rwa [abs_of_nonneg (by linarith only [hlamtau] : (0 : ℝ) ≤ tau - lam)] at hbound

/-- For positive `x`, the logarithmic-kernel integral over a fixed horizontal
segment `[lam,tau] ⊆ [-1/2,2]` tends to zero along `goodHeightSeq`. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_goodHeightSeq {x : ℝ} (hx : 0 < x)
    {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun j : ℕ =>
        ∫ σ in lam..tau,
          riemannZetaLogContourKernel x
            (σ + goodHeightSeq j * Complex.I))
      Filter.atTop (nhds 0) := by
  set M : ℝ := max (x ^ (-(1 : ℝ) / 2)) (x ^ (2 : ℝ)) with hM_def
  have hbtend :
    Filter.Tendsto
      (fun j : ℕ =>
        Real.log (goodHeightSeq j + 2) ^ 2 /
          (goodHeightSeq j) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_log_add_two_sq_div_sq_atTop.comp
      tendsto_goodHeightSeq_atTop
  have hg :
    ∀ T : ℝ,
      qMinusOneZetaLogDerivConst *
              Real.log (T + 2) ^ 2 *
              M /
            T ^ 2 *
          (tau - lam) =
        (qMinusOneZetaLogDerivConst * M *
            (tau - lam)) *
          (Real.log (T + 2) ^ 2 / T ^ 2) := by
    intro T; ring
  have hatend :
    Filter.Tendsto
      (fun j : ℕ =>
        qMinusOneZetaLogDerivConst *
              Real.log (goodHeightSeq j + 2) ^ 2 *
              M /
            (goodHeightSeq j) ^ 2 *
          (tau - lam))
      Filter.atTop (nhds 0) := by
    simp_rw [hg]
    simpa only [mul_zero] using
      hbtend.const_mul
        (qMinusOneZetaLogDerivConst * M * (tau - lam))
  exact
    squeeze_zero_norm
      (fun j =>
        norm_intervalIntegral_riemannZetaLogContourKernel_good_height_le
          hx (le_add_of_nonneg_right (Nat.cast_nonneg j))
          (goodHeightSeq_mem j)
          (goodHeightSeq_good j) hlam hlamtau htau)
      hatend

/-- The reciprocal-kernel analogue of
`RiemannZeta.tendsto_intervalIntegral_riemannZetaLogContourKernel_goodHeightSeq`. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_goodHeightSeq {x : ℝ}
    (hx : 0 < x) {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun j : ℕ =>
        ∫ σ in lam..tau,
          riemannZetaReciprocalContourKernel x
            (σ + goodHeightSeq j * Complex.I))
      Filter.atTop (nhds 0) := by
  set M : ℝ := max (x ^ (-(3 : ℝ) / 2)) (x ^ (1 : ℝ)) with hM_def
  have hbtend :
    Filter.Tendsto
      (fun j : ℕ =>
        Real.log (goodHeightSeq j + 2) ^ 2 /
          (goodHeightSeq j) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_log_add_two_sq_div_sq_atTop.comp
      tendsto_goodHeightSeq_atTop
  have hg :
    ∀ T : ℝ,
      qMinusOneZetaLogDerivConst *
              Real.log (T + 2) ^ 2 *
              M /
            T ^ 2 *
          (tau - lam) =
        (qMinusOneZetaLogDerivConst * M *
            (tau - lam)) *
          (Real.log (T + 2) ^ 2 / T ^ 2) := by
    intro T; ring
  have hatend :
    Filter.Tendsto
      (fun j : ℕ =>
        qMinusOneZetaLogDerivConst *
              Real.log (goodHeightSeq j + 2) ^ 2 *
              M /
            (goodHeightSeq j) ^ 2 *
          (tau - lam))
      Filter.atTop (nhds 0) := by
    simp_rw [hg]
    simpa only [mul_zero] using
      hbtend.const_mul
        (qMinusOneZetaLogDerivConst * M * (tau - lam))
  exact
    squeeze_zero_norm
      (fun j =>
        norm_intervalIntegral_riemannZetaReciprocalContourKernel_good_height_le
          hx (le_add_of_nonneg_right (Nat.cast_nonneg j))
          (goodHeightSeq_mem j)
          (goodHeightSeq_good j) hlam hlamtau htau)
      hatend

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
