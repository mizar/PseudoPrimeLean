/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SincErrorIntegral
import PseudoPrime.Analysis.MovingPrimitiveParts
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountIntegratedTailRH
import all PseudoPrime.Analysis.SineMajorant

/-! # Integrated zero-count error for the smoothed tail -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Integrating the count discrepancy against the scaled kernel gives a boundary
term and an integral against its moving primitive, including endpoints at zeros. -/
theorem sincCountError_parts (hRH : RiemannHypothesis) {β T R : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    let P := fun t ↦ ∫ y in T..t, zeroCountError y
    (∫ t in T..R, β ^ 2 * Analysis.sincErrorKernel (β * t) * zeroCountError t) =
      β ^ 2 * Analysis.sincErrorKernel (β * R) * P R -
        ∫ t in T..R, β ^ 3 * deriv Analysis.sincErrorKernel (β * t) * P t := by
  intro P
  have hp {t : ℝ} (ht : t ∈ Set.Icc T R) : 0 < β * t :=
    mul_pos hb (lt_of_lt_of_le (by linarith only [hT] : 0 < T) ht.1)
  apply Analysis.integral_mul_of_moving_primitive hTR (zeroCountError_intervalIntegrable hRH hT hTR)
  · apply ContDiffOn.absolutelyContinuousOnInterval
    rw [Set.uIcc_of_le hTR]
    have hd : ContDiff ℝ 2 Analysis.sineMajorant := by
      unfold Analysis.sineMajorant; fun_prop
    have hd' : ContDiff ℝ 1 (deriv Analysis.sineMajorant) := hd.deriv'
    have hscale : ContDiff ℝ 1 (fun t : ℝ ↦ β * t) := contDiff_const.mul contDiff_id
    have h₀ : ContDiffOn ℝ 1 (fun t : ℝ ↦ Analysis.sineMajorant (β * t)) (Set.Icc T R) :=
      ((hd.of_le (by decide : (1 : WithTop ℕ∞) ≤ 2)).comp hscale).contDiffOn
    have h₁ : ContDiffOn ℝ 1 (fun t : ℝ ↦ deriv Analysis.sineMajorant (β * t)) (Set.Icc T R) :=
      (hd'.comp hscale).contDiffOn
    unfold Analysis.sincErrorKernel
    exact
      contDiffOn_const.mul
        (((contDiffOn_const.add h₁).div (hscale.contDiffOn.pow 2)
              (fun t ht ↦ pow_ne_zero _ (hp ht).ne')).sub
          ((contDiffOn_const.mul (h₀.add contDiffOn_const)).div (hscale.contDiffOn.pow 3)
            (fun t ht ↦ pow_ne_zero _ (hp ht).ne')))
  · intro t ht
    have hd := (Analysis.hasDerivAt_sincErrorKernel (hp ht)).differentiableAt.hasDerivAt
    apply ((hd.comp t ((hasDerivAt_id t).const_mul β)).const_mul (β ^ 2)).congr_deriv
    ring

private theorem kernel_scaled_abs {z : ℝ} (hz : 1 ≤ z) :
    |z ^ 2 * Analysis.sincErrorKernel z| ≤ 5 := by
  have hp := zero_lt_one.trans_le hz
  have he :
    z ^ 2 * Analysis.sincErrorKernel z =
      1 + deriv Analysis.sineMajorant z -
        2 * (Analysis.sineMajorant z + Analysis.sineMajorantShift) / z := by
    unfold Analysis.sincErrorKernel
    field_simp [hp.ne']
  have hn :=
    add_nonneg ((abs_nonneg _).trans (Analysis.abs_sin_le_majorant z))
      Analysis.sineMajorantShift_bounds.1.le
  have hu : 2 * (Analysis.sineMajorant z + Analysis.sineMajorantShift) / z ≤ 3 := by
    apply (div_le_iff₀ hp).2
    linarith only [hz, Analysis.sineMajorant_le_one z, Analysis.sineMajorantShift_bounds.2]
  have hd := abs_le.mp (Analysis.abs_deriv_sineMajorant_le z)
  rw [he]
  have hnon := div_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hn) hp.le
  exact abs_le.mpr ⟨by linarith only [hu, hd.1], by linarith only [hd.2, hnon]⟩

/-- Under RH the upper boundary term of the second integration by parts vanishes
for every positive smoothing scale, by comparison with the inverse-square endpoint. -/
theorem sincCountError_endpoint (hRH : RiemannHypothesis) {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T) :
    Filter.Tendsto
      (fun R ↦ β ^ 2 * Analysis.sincErrorKernel (β * R) * (∫ y in T..R, zeroCountError y))
      Filter.atTop (nhds 0) := by
  have hm := (zeroCountError_invSq_endpoint_tendsto hRH hT).abs.const_mul (5 : ℝ)
  simp only [abs_zero, mul_zero] at hm
  apply squeeze_zero_norm' _ hm
  filter_upwards [Filter.eventually_ge_atTop (1 / β)] with R hR
  have hz : 1 ≤ β * R := by linarith only [(div_le_iff₀ hb).mp hR]
  have hp := (div_pos zero_lt_one hb).trans_le hR
  let P := ∫ y in T..R, zeroCountError y
  have he :
    β ^ 2 * Analysis.sincErrorKernel (β * R) * P =
      ((β * R) ^ 2 * Analysis.sincErrorKernel (β * R)) * (R⁻¹ ^ 2 * P) := by
    field_simp [hp.ne']
  change |β ^ 2 * Analysis.sincErrorKernel (β * R) * P| ≤ 5 * |R⁻¹ ^ 2 * P|
  rw [he, abs_mul]
  exact mul_le_mul_of_nonneg_right (kernel_scaled_abs hz) (abs_nonneg _)

/-- With the scaled lower endpoint fixed at two fifths, the majorant for the
moving-primitive integral costs the squared scale times the explicit error budget. -/
theorem sincCountError_majorant {β T R : ℝ} (hb : 0 < β) (hT : 100 ≤ T) (hc : β * T = 2 / 5)
    (hTR : T ≤ R) :
    (∫ t in T..R,
        β ^ 3 * |deriv Analysis.sincErrorKernel (β * t)| *
          (16 + 7 / 5 * Real.log T + 9 / 5 * Real.log (t / T))) ≤
      β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) := by
  let A := 16 + 7 / 5 * Real.log T
  let f := fun z : ℝ ↦ (9 / 5 * Real.log (z / (2 / 5)) + A) * |deriv Analysis.sincErrorKernel z|
  have ha : 0 ≤ A := by
    dsimp only [A]
    linarith only [Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 100).trans hT)]
  have hR := mul_le_mul_of_nonneg_left hTR hb.le
  rw [hc] at hR
  have hu := Analysis.sincError_weighted_integral hR (by norm_num only : (0 : ℝ) ≤ 9 / 5) ha
  have he (t : ℝ) : β * t / (2 / 5) = t / T := by
    rw [← hc]; field_simp [hb.ne']
  calc
    _ = ∫ t in T..R, β ^ 2 * (β * f (β * t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [f, A]
      rw [he]
      ring
    _ = β ^ 2 * (∫ z in β * T..β * R, f z) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ←
        intervalIntegral.smul_integral_comp_mul_left f β, smul_eq_mul]
    _ ≤ _ := by
      rw [hc]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
      convert hu using 1
      ring

/-- Under RH the primitive term in the second Abel formula satisfies the
quadratic error allowance uniformly in the finite upper endpoint. -/
private theorem remainder_norm_bound (hRH : RiemannHypothesis) {β T R : ℝ} (hb : 0 < β)
    (hT : 100 ≤ T) (hc : β * T = 2 / 5) (hTR : T ≤ R) :
    let g := fun t ↦
      β ^ 3 * deriv Analysis.sincErrorKernel (β * t) * (∫ y in T..t, zeroCountError y)
    IntervalIntegrable g MeasureTheory.volume T R ∧
      (∫ t in T..R, ‖g t‖) ≤ β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) := by
  intro g
  let P := fun t ↦ ∫ y in T..t, zeroCountError y
  have hp : 0 < T := by linarith only [hT]
  have hQ := zeroCountError_intervalIntegrable hRH hT hTR
  have hP := (hQ.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc).continuousOn
  have hd : ContDiff ℝ 2 Analysis.sineMajorant := by
    unfold Analysis.sineMajorant; fun_prop
  have h₁ : ContDiff ℝ 1 (deriv Analysis.sineMajorant) := hd.deriv'
  have h₂ : ContDiff ℝ 0 (deriv (deriv Analysis.sineMajorant)) := h₁.deriv'
  have hK : ContinuousOn (fun t ↦ deriv Analysis.sincErrorKernel (β * t)) (Set.uIcc T R) := by
    have hz {t : ℝ} (ht : t ∈ Set.uIcc T R) :=
      mul_pos hb (hp.trans_le ((Set.uIcc_of_le hTR) ▸ ht : t ∈ Set.Icc T R).1)
    apply ContinuousOn.congr _ (fun t ht ↦ (Analysis.hasDerivAt_sincErrorKernel (hz ht)).deriv)
    intro t ht
    have h0 := hd.continuous
    have h1 := h₁.continuous
    have h2 := h₂.continuous
    fun_prop (disch := exact pow_ne_zero _ (hz ht).ne')
  have hB :
    ContinuousOn (fun t ↦ 16 + 7 / 5 * Real.log T + 9 / 5 * Real.log (t / T)) (Set.uIcc T R) := by
    intro t ht
    have ht' := hp.trans_le ((Set.uIcc_of_le hTR) ▸ ht : t ∈ Set.Icc T R).1
    fun_prop (disch :=
      first
      | exact hp.ne'
      | exact div_ne_zero ht'.ne' hp.ne')
  have hconst : ContinuousOn (fun _ : ℝ ↦ β ^ 3) (Set.uIcc T R) := continuousOn_const
  have hi := ((hconst.mul hK).mul hP).intervalIntegrable (μ := MeasureTheory.volume)
  have hm := ((hconst.mul hK.abs).mul hB).intervalIntegrable (μ := MeasureTheory.volume)
  refine ⟨hi, ?_⟩
  apply
    le_trans (intervalIntegral.integral_mono_on hTR hi.norm hm ?_)
      (sincCountError_majorant hb hT hc hTR)
  intro t ht
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hb.le 3)]
  exact
    mul_le_mul_of_nonneg_left (zeroCountError_moving_bound hRH hT ht.1)
      (mul_nonneg (pow_nonneg hb.le 3) (abs_nonneg _))

/-- Under RH the finite primitive remainder satisfies the quadratic error budget. -/
theorem sincCountError_remainder (hRH : RiemannHypothesis) {β T R : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hc : β * T = 2 / 5) (hTR : T ≤ R) :
    |∫ t in T..R,
          β ^ 3 * deriv Analysis.sincErrorKernel (β * t) * (∫ y in T..t, zeroCountError y)| ≤
      β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) := by
  exact
    (intervalIntegral.norm_integral_le_integral_norm hTR).trans
      (remainder_norm_bound hRH hb hT hc hTR).2

/-- Under RH the primitive remainder is absolutely integrable above the cutoff. -/
theorem sincCountError_integrable (hRH : RiemannHypothesis) {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hc : β * T = 2 / 5) :
    MeasureTheory.IntegrableOn
      (fun t ↦ β ^ 3 * deriv Analysis.sincErrorKernel (β * t) * (∫ y in T..t, zeroCountError y))
      (Set.Ioi T) := by
  apply
    MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5)) T _ (Filter.tendsto_id (α := ℝ)) _
  · intro R
    by_cases h : T ≤ R
    · exact (remainder_norm_bound hRH hb hT hc h).1.1
    · rw [id_eq, Set.Ioc_eq_empty (not_lt_of_ge (le_of_not_ge h))]
      exact MeasureTheory.integrableOn_empty
  · filter_upwards [Filter.eventually_ge_atTop T] with R h
    exact (remainder_norm_bound hRH hb hT hc h).2

/-- Under RH the count-error integral converges, with the same quadratic allowance
as the primitive remainder, since the upper boundary term tends to zero. -/
theorem sincCountError_limit (hRH : RiemannHypothesis) {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hc : β * T = 2 / 5) :
    ∃ L : ℝ,
      Filter.Tendsto
          (fun R ↦ ∫ t in T..R, β ^ 2 * Analysis.sincErrorKernel (β * t) * zeroCountError t)
          Filter.atTop (nhds L) ∧
        |L| ≤ β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) := by
  have hi :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi T (sincCountError_integrable hRH hb hT hc)
      (Filter.tendsto_id (α := ℝ))
  have hd := (sincCountError_endpoint hRH hb hT).sub hi
  rw [zero_sub] at hd
  refine ⟨_, hd.congr' ?_, ?_⟩
  · filter_upwards [Filter.eventually_ge_atTop T] with R h
    exact (sincCountError_parts hRH hb hT h).symm
  · rw [abs_neg]
    apply le_of_tendsto hi.abs
    filter_upwards [Filter.eventually_ge_atTop T] with R h
    exact sincCountError_remainder hRH hb hT hc h

/-- The reciprocal discrepancy and the discrepancy in weighted Abel summation
combine to the scaled error kernel on every finite interval above the cutoff. -/
theorem sincCountError_weight_split (hRH : RiemannHypothesis) {β T R : ℝ} (hb : 0 < β)
    (hT : 100 ≤ T) (hTR : T ≤ R) :
    (∫ t in T..R, t⁻¹ ^ 2 * zeroCountError t) +
        (∫ t in T..R, zeroCountError t * deriv (Analysis.sincTailWeight β) t) =
      ∫ t in T..R, β ^ 2 * Analysis.sincErrorKernel (β * t) * zeroCountError t := by
  have hp : 0 < T := lt_of_lt_of_le (by norm_num only) hT
  have ht {t : ℝ} (h : t ∈ Set.uIcc T R) : 0 < t :=
    hp.trans_le ((Set.uIcc_of_le hTR) ▸ h : t ∈ Set.Icc T R).1
  have hi := zeroCountError_intervalIntegrable hRH hT hTR
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc T R) :=
    (continuousOn_id.inv₀ (fun t h ↦ (ht h).ne')).pow 2
  rw [←
    intervalIntegral.integral_add (hi.continuousOn_mul hc)
      (hi.mul_continuousOn (Analysis.continuousOn_deriv_sincTail hb.ne' hp hTR))]
  apply intervalIntegral.integral_congr
  intro t h
  dsimp only
  rw [← Analysis.sincErrorKernel_scale hb (ht h), one_div, inv_pow, add_mul,
    mul_comm (zeroCountError t)]

/-- The discrepancy integral for the Abel weight converges to the combined error
minus the reciprocal discrepancy. Only the combined error spends the quadratic budget. -/
theorem sincCountError_weight_limit (hRH : RiemannHypothesis) {β T : ℝ} (hb : 0 < β) (hT : 100 ≤ T)
    (hc : β * T = 2 / 5) :
    ∃ L : ℝ,
      |L| ≤ β ^ 2 * (57 * (16 + 7 / 5 * Real.log T) + 234 / 5) ∧
        Filter.Tendsto (fun R ↦ ∫ t in T..R, zeroCountError t * deriv (Analysis.sincTailWeight β) t)
          Filter.atTop
          (nhds (L - ∫ t in Set.Ioi T, (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y))) := by
  obtain ⟨L, hl, hB⟩ := sincCountError_limit hRH hb hT hc
  refine ⟨L, hB, (hl.sub (zeroCountError_invSq_tendsto hRH hT)).congr' ?_⟩
  filter_upwards [Filter.eventually_ge_atTop T] with R h
  exact sub_eq_of_eq_add' (sincCountError_weight_split hRH hb hT h).symm

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
