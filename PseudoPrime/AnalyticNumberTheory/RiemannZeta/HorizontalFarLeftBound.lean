/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FarLeftLogDeriv
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SmoothedContour
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.Growth
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GrowthBounds
import PseudoPrime.AnalyticNumberTheory.Gamma.GrowthElementary
import PseudoPrime.AnalyticNumberTheory.General.GeometricDecay

/-!
# Far-left horizontal contour estimates

Combine the logarithmic-derivative majorant on `[-(2m+1),-1/2]+it` with the
power and denominator bounds for both kernels. For `x > 1`, integration and
the chosen growing height sequence make these horizontal integrals vanish.
-/

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
  have hxpos : (0 : ℝ) < x := by linarith
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
    rw [← sq_abs t]; exact pow_le_pow_left₀ (abs_nonneg t) hznorm_ge 2
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
    have hm := Nat.cast_nonneg (α := ℝ) m; linarith only [hm]
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := -(2 * (m : ℝ) + 1)) (b := -1 / 2) (f :=
      fun σ : ℝ => riemannZetaLogContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) (C :=
      farLeftZetaLogDerivBound m t * x ^ (-(1 : ℝ) / 2) / t ^ 2)
      (by
        rw [Set.uIoc_of_le hlamtau]
        rintro σ ⟨hσ1, hσ2⟩
        exact norm_riemannZetaLogContourKernel_farLeft_le hx ⟨hσ1.le, hσ2⟩ ht)
  rwa [abs_of_nonneg
      (by linarith only [hlamtau] : (0 : ℝ) ≤ -1 / 2 - (-(2 * (m : ℝ) + 1)))] at hbound

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
    have hm := Nat.cast_nonneg (α := ℝ) m; linarith only [hm]
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := -(2 * (m : ℝ) + 1)) (b := -1 / 2) (f :=
      fun σ : ℝ => riemannZetaReciprocalContourKernel x ((σ : ℂ) + (t : ℂ) * Complex.I)) (C :=
      farLeftZetaLogDerivBound m t * x ^ (-(3 : ℝ) / 2) / t ^ 2)
      (by
        rw [Set.uIoc_of_le hlamtau]
        rintro σ ⟨hσ1, hσ2⟩
        exact norm_riemannZetaReciprocalContourKernel_farLeft_le hx ⟨hσ1.le, hσ2⟩ ht)
  rwa [abs_of_nonneg
      (by linarith only [hlamtau] : (0 : ℝ) ≤ -1 / 2 - (-(2 * (m : ℝ) + 1)))] at hbound

/-- For fixed `x > 1`, the logarithmic-kernel integral over the growing
segment `[-(2m+1),-1/2]+i*farLeftHeightSeq(m)` tends to zero. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_farLeftHeightSeq {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaLogContourKernel x ((σ : ℂ) + (farLeftHeightSeq m : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  set A : ℝ := qMinusOneHorizontalFarLeftConst with hA_def
  set D0 : ℝ := Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi / 2) ^ 2) with hD0_def
  have hD0nn : (0 : ℝ) ≤ D0 := by
    rw [hD0_def]; positivity
  set K : ℝ := (|A| + D0) + (1 + 20 * Real.pi) with hK_def
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK_def]; positivity
  have hbound :
    ∀ m : ℕ,
      ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
            riemannZetaLogContourKernel x ((σ : ℂ) + (farLeftHeightSeq m : ℂ) * Complex.I)‖ ≤
        K * x ^ (-(1 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m := by
    intro m
    set T : ℝ := farLeftHeightSeq m with hT_def
    have hT1 : (1 : ℝ) ≤ T := one_le_farLeftHeightSeq m
    have hTpos : (0 : ℝ) < T := farLeftHeightSeq_pos m
    have hTne : T ≠ 0 := hTpos.ne'
    have hbase :=
      norm_intervalIntegral_riemannZetaLogContourKernel_farLeft_le hx (m := m) (t := T) hTne
    have hD_le : Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi * T / 2) ^ 2) ≤ D0 := by
      rw [hD0_def]
      have hsinh_mono : Real.sinh (Real.pi / 2) ≤ Real.sinh (Real.pi * T / 2) :=
        Real.sinh_le_sinh.mpr (by nlinarith only [Real.pi_pos, hT1])
      have hsinh_pos : (0 : ℝ) < Real.sinh (Real.pi / 2) := by
        rw [show (0 : ℝ) = Real.sinh 0 from Real.sinh_zero.symm]
        exact Real.sinh_lt_sinh.mpr (by positivity)
      gcongr
    have hB_le : farLeftBTerm m ≤ T := farLeftBTerm_le_farLeftHeightSeq m
    have hA_le : A ≤ |A| := le_abs_self A
    have hfarLeft_le : farLeftZetaLogDerivBound m T ≤ (|A| + D0) + (1 + 20 * Real.pi) * T := by
      unfold farLeftZetaLogDerivBound
      rw [← hA_def, abs_of_pos hTpos]
      nlinarith only [hA_le, hD_le, hB_le]
    have hxσ_pos : (0 : ℝ) < x ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith [hTpos]) _
    have hratio_le :
      ((|A| + D0) + (1 + 20 * Real.pi) * T) * x ^ (-(1 : ℝ) / 2) / T ^ 2 ≤
        K * x ^ (-(1 : ℝ) / 2) / T := by
      rw [hK_def, div_le_div_iff₀ (by positivity) hTpos]
      have hT2 : T ≤ T ^ 2 := by nlinarith only [hT1]
      have haux : 0 ≤ (|A| + D0) * x ^ (-(1 : ℝ) / 2) * T * (T - 1) := by positivity
      nlinarith only [haux]
    calc
      ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
              riemannZetaLogContourKernel x ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          farLeftZetaLogDerivBound m T * x ^ (-(1 : ℝ) / 2) / T ^ 2 *
            (-1 / 2 - (-(2 * (m : ℝ) + 1))) :=
        hbase
      _ = farLeftZetaLogDerivBound m T * x ^ (-(1 : ℝ) / 2) / T ^ 2 * (2 * (m : ℝ) + 1 / 2) := by
        ring_nf
      _ ≤
          (((|A| + D0) + (1 + 20 * Real.pi) * T) * x ^ (-(1 : ℝ) / 2) / T ^ 2) *
            (2 * (m : ℝ) + 1 / 2) :=
        by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hfarLeft_le hxσ_pos.le
      _ ≤ (K * x ^ (-(1 : ℝ) / 2) / T) * (2 * (m : ℝ) + 1 / 2) := by
        apply mul_le_mul_of_nonneg_right hratio_le (by positivity)
      _ = K * x ^ (-(1 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / T := by ring
  have htend :
    Filter.Tendsto
      (fun m : ℕ => K * x ^ (-(1 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m)
      Filter.atTop (nhds 0) := by
    have hL_le : ∀ m : ℕ, 2 * (m : ℝ) + 1 / 2 ≤ 3 * ((m : ℝ) + 1) := fun m => by
      linarith only [Nat.cast_nonneg (α := ℝ) m]
    have hratio_le :
      ∀ m : ℕ,
        K * x ^ (-(1 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m ≤
          3 * (K * x ^ (-(1 : ℝ) / 2)) / (farLeftBTerm m + 1) := by
      intro m
      have hKxnn : (0 : ℝ) ≤ K * x ^ (-(1 : ℝ) / 2) := by positivity
      have h1 :
        K * x ^ (-(1 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) ≤
          K * x ^ (-(1 : ℝ) / 2) * (3 * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hL_le m) hKxnn
      have h3 : (0 : ℝ) < farLeftBTerm m + 1 := by linarith only [farLeftBTerm_pos m]
      calc
        K * x ^ (-(1 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m ≤
            K * x ^ (-(1 : ℝ) / 2) * (3 * ((m : ℝ) + 1)) / farLeftHeightSeq m :=
          div_le_div_of_nonneg_right h1 (farLeftHeightSeq_pos m).le
        _ = 3 * (K * x ^ (-(1 : ℝ) / 2)) * ((m : ℝ) + 1) / farLeftHeightSeq m := by ring
        _ = 3 * (K * x ^ (-(1 : ℝ) / 2)) * ((m : ℝ) + 1) / (((m : ℝ) + 1) * (farLeftBTerm m + 1)) :=
          by simp only [farLeftHeightSeq]
        _ = 3 * (K * x ^ (-(1 : ℝ) / 2)) / (farLeftBTerm m + 1) := by
          have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
          field_simp
    have hden_tend : Filter.Tendsto (fun m : ℕ => farLeftBTerm m + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_farLeftBTerm_atTop
    have hrhs_tend :
      Filter.Tendsto (fun m : ℕ => 3 * (K * x ^ (-(1 : ℝ) / 2)) / (farLeftBTerm m + 1)) Filter.atTop
        (nhds 0) := by
      simpa only [div_eq_mul_inv, neg_mul, one_mul, Pi.inv_apply, mul_zero] using
        (hden_tend.inv_tendsto_atTop).const_mul (3 * (K * x ^ (-(1 : ℝ) / 2)))
    exact
      squeeze_zero (fun m => div_nonneg (by positivity) (farLeftHeightSeq_pos m).le) hratio_le
        hrhs_tend
  exact squeeze_zero_norm hbound htend

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`tendsto_intervalIntegral_riemannZetaLogContourKernel_farLeftHeightSeq`: the only change is the
fixed exponent `x ^ (-3/2)` in place of `x ^ (-1/2)`, since
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.norm_riemannZetaReciprocalContourKernel_farLeft_le`
bounds `x ^ (σ - 1)` (`σ ≤ -1/2`) rather than `x ^ σ`. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_farLeftHeightSeq {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaReciprocalContourKernel x ((σ : ℂ) + (farLeftHeightSeq m : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  set A : ℝ := qMinusOneHorizontalFarLeftConst with hA_def
  set D0 : ℝ := Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi / 2) ^ 2) with hD0_def
  have hD0nn : (0 : ℝ) ≤ D0 := by
    rw [hD0_def]; positivity
  set K : ℝ := (|A| + D0) + (1 + 20 * Real.pi) with hK_def
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hK_def]; positivity
  have hbound :
    ∀ m : ℕ,
      ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
            riemannZetaReciprocalContourKernel x ((σ : ℂ) + (farLeftHeightSeq m : ℂ) * Complex.I)‖ ≤
        K * x ^ (-(3 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m := by
    intro m
    set T : ℝ := farLeftHeightSeq m with hT_def
    have hT1 : (1 : ℝ) ≤ T := one_le_farLeftHeightSeq m
    have hTpos : (0 : ℝ) < T := farLeftHeightSeq_pos m
    have hTne : T ≠ 0 := hTpos.ne'
    have hbase :=
      norm_intervalIntegral_riemannZetaReciprocalContourKernel_farLeft_le hx (m := m) (t := T) hTne
    have hD_le : Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi * T / 2) ^ 2) ≤ D0 := by
      rw [hD0_def]
      have hsinh_mono : Real.sinh (Real.pi / 2) ≤ Real.sinh (Real.pi * T / 2) :=
        Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos])
      have hsinh_pos : (0 : ℝ) < Real.sinh (Real.pi / 2) := by
        rw [show (0 : ℝ) = Real.sinh 0 from Real.sinh_zero.symm]
        exact Real.sinh_lt_sinh.mpr (by positivity)
      gcongr
    have hB_le : farLeftBTerm m ≤ T := farLeftBTerm_le_farLeftHeightSeq m
    have hA_le : A ≤ |A| := le_abs_self A
    have hfarLeft_le : farLeftZetaLogDerivBound m T ≤ (|A| + D0) + (1 + 20 * Real.pi) * T := by
      unfold farLeftZetaLogDerivBound
      rw [← hA_def, abs_of_pos hTpos]
      nlinarith [hA_le, hD_le, hB_le]
    have hxσ_pos : (0 : ℝ) < x ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    have hratio_le :
      ((|A| + D0) + (1 + 20 * Real.pi) * T) * x ^ (-(3 : ℝ) / 2) / T ^ 2 ≤
        K * x ^ (-(3 : ℝ) / 2) / T := by
      rw [hK_def, div_le_div_iff₀ (by positivity) hTpos]
      have hT2 : T ≤ T ^ 2 := by nlinarith
      have haux : 0 ≤ (|A| + D0) * x ^ (-(3 : ℝ) / 2) * T * (T - 1) := by positivity
      nlinarith only [haux]
    calc
      ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
              riemannZetaReciprocalContourKernel x ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          farLeftZetaLogDerivBound m T * x ^ (-(3 : ℝ) / 2) / T ^ 2 *
            (-1 / 2 - (-(2 * (m : ℝ) + 1))) :=
        hbase
      _ = farLeftZetaLogDerivBound m T * x ^ (-(3 : ℝ) / 2) / T ^ 2 * (2 * (m : ℝ) + 1 / 2) := by
        ring_nf
      _ ≤
          (((|A| + D0) + (1 + 20 * Real.pi) * T) * x ^ (-(3 : ℝ) / 2) / T ^ 2) *
            (2 * (m : ℝ) + 1 / 2) :=
        by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hfarLeft_le hxσ_pos.le
      _ ≤ (K * x ^ (-(3 : ℝ) / 2) / T) * (2 * (m : ℝ) + 1 / 2) := by
        apply mul_le_mul_of_nonneg_right hratio_le (by positivity)
      _ = K * x ^ (-(3 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / T := by ring
  have htend :
    Filter.Tendsto
      (fun m : ℕ => K * x ^ (-(3 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m)
      Filter.atTop (nhds 0) := by
    have hL_le : ∀ m : ℕ, 2 * (m : ℝ) + 1 / 2 ≤ 3 * ((m : ℝ) + 1) := fun m => by linarith
    have hratio_le :
      ∀ m : ℕ,
        K * x ^ (-(3 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m ≤
          3 * (K * x ^ (-(3 : ℝ) / 2)) / (farLeftBTerm m + 1) := by
      intro m
      have hKxnn : (0 : ℝ) ≤ K * x ^ (-(3 : ℝ) / 2) := by positivity
      have h1 :
        K * x ^ (-(3 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) ≤
          K * x ^ (-(3 : ℝ) / 2) * (3 * ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (hL_le m) hKxnn
      have h3 : (0 : ℝ) < farLeftBTerm m + 1 := by linarith [farLeftBTerm_pos m]
      calc
        K * x ^ (-(3 : ℝ) / 2) * (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m ≤
            K * x ^ (-(3 : ℝ) / 2) * (3 * ((m : ℝ) + 1)) / farLeftHeightSeq m :=
          div_le_div_of_nonneg_right h1 (farLeftHeightSeq_pos m).le
        _ = 3 * (K * x ^ (-(3 : ℝ) / 2)) * ((m : ℝ) + 1) / farLeftHeightSeq m := by ring
        _ = 3 * (K * x ^ (-(3 : ℝ) / 2)) * ((m : ℝ) + 1) / (((m : ℝ) + 1) * (farLeftBTerm m + 1)) :=
          by simp only [farLeftHeightSeq]
        _ = 3 * (K * x ^ (-(3 : ℝ) / 2)) / (farLeftBTerm m + 1) := by
          have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
          field_simp
    have hden_tend : Filter.Tendsto (fun m : ℕ => farLeftBTerm m + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_farLeftBTerm_atTop
    have hrhs_tend :
      Filter.Tendsto (fun m : ℕ => 3 * (K * x ^ (-(3 : ℝ) / 2)) / (farLeftBTerm m + 1)) Filter.atTop
        (nhds 0) := by
      simpa only [div_eq_mul_inv, neg_mul, Pi.inv_apply, mul_zero] using
        (hden_tend.inv_tendsto_atTop).const_mul (3 * (K * x ^ (-(3 : ℝ) / 2)))
    exact
      squeeze_zero (fun m => div_nonneg (by positivity) (farLeftHeightSeq_pos m).le) hratio_le
        hrhs_tend
  exact squeeze_zero_norm hbound htend

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
