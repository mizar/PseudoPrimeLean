/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaLogBoundaryIntegralRH
public import PseudoPrime.Analysis.CombinedZeroWeight
import PseudoPrime.Analysis.MovingPrimitiveParts
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountArgumentIntegralRH

/-! # Moving count-argument primitives and the combined zero weight -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and for `100 ≤ T ≤ R`, integration by parts transfers the
combined zero weight from twice the count-defined argument to its moving
primitive. The primitive may have only an almost-everywhere derivative;
no continuity of the zero-count argument is assumed. -/
theorem combined_weight_countArg_parts (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    (∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * zetaArgCount t)) =
      Analysis.combinedZeroWeight T R * (∫ t in T..R, 2 * zetaArgCount t) -
        ∫ t in T..R, Analysis.combinedZeroWeightDeriv T t * (∫ y in T..t, 2 * zetaArgCount y) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hf := (zetaArgCount_integrable hRH hT0 hTR).const_mul 2
  have hw := Analysis.combinedZeroWeight_absContinuous hT0 hTR
  apply Analysis.integral_mul_of_moving_primitive hTR hf hw
  intro t ht
  exact Analysis.combinedZeroWeight_hasDerivAt (hT0.trans_le ht.1).ne'

/-- Under RH, the weighted count-argument integral on a finite interval
is bounded by its endpoint contribution and the variation of the weight
against the scale-separated moving-primitive budget. This keeps the
derivative's sign change inside a single absolute-value integral. -/
theorem combined_weight_countArg_finite_bound (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    |∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * zetaArgCount t)| ≤
      |Analysis.combinedZeroWeight T R| *
          (16 + (7 / 5 : ℝ) * Real.log T + (7 / 5 : ℝ) * Real.log (R / T)) +
        ∫ t in T..R,
          |Analysis.combinedZeroWeightDeriv T t| *
            (16 + (7 / 5 : ℝ) * Real.log T + (7 / 5 : ℝ) * Real.log (t / T)) := by
  have hT0 : 0 < T := by linarith only [hT]
  let P : ℝ → ℝ := fun t ↦ ∫ y in T..t, 2 * zetaArgCount y
  let B : ℝ → ℝ := fun t ↦ 16 + (7 / 5 : ℝ) * Real.log T + (7 / 5 : ℝ) * Real.log (t / T)
  have hf := (zetaArgCount_integrable hRH hT0 hTR).const_mul 2
  have hP : AbsolutelyContinuousOnInterval P T R :=
    hf.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  have hd := Analysis.combinedZeroWeightDeriv_continuousOn (R := R) hT0
  have hi :
    IntervalIntegrable (fun t ↦ Analysis.combinedZeroWeightDeriv T t * P t) MeasureTheory.volume T
      R := by
    have hiw := hd.intervalIntegrable_of_Icc hTR (μ := MeasureTheory.volume)
    have hpcont := hP.continuousOn
    exact hiw.mul_continuousOn hpcont
  have hB : ContinuousOn B (Set.Icc T R) := by
    intro t ht
    have hlog : ContinuousAt (fun x : ℝ ↦ Real.log (x / T)) t :=
      ContinuousAt.comp (f := fun x : ℝ ↦ x / T)
        (Real.continuousAt_log (div_ne_zero (hT0.trans_le ht.1).ne' hT0.ne'))
        (continuousAt_id.div_const T)
    exact ((continuousAt_const.add (continuousAt_const.mul hlog))).continuousWithinAt
  have hmajor :
    IntervalIntegrable (fun t ↦ |Analysis.combinedZeroWeightDeriv T t| * B t) MeasureTheory.volume T
      R :=
    (hd.abs.mul hB).intervalIntegrable_of_Icc hTR
  have hpoint :
    ∀ t ∈ Set.Icc T R,
      ‖Analysis.combinedZeroWeightDeriv T t * P t‖ ≤
        |Analysis.combinedZeroWeightDeriv T t| * B t := by
    intro t ht
    have hp := countArg_moving_integral_bound hRH hT ht.1
    change |P t| ≤ B t at hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  have hintegral := intervalIntegral.integral_mono_on hTR hi.norm hmajor hpoint
  have hnorm :=
    intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := fun t ↦
      Analysis.combinedZeroWeightDeriv T t * P t) hTR
  rw [Real.norm_eq_abs] at hnorm
  have hbound :
    |∫ t in T..R, Analysis.combinedZeroWeightDeriv T t * P t| ≤
      ∫ t in T..R, |Analysis.combinedZeroWeightDeriv T t| * B t :=
    hnorm.trans hintegral
  have hend := countArg_moving_integral_bound hRH hT hTR
  change |P R| ≤ B R at hend
  have hmul := mul_le_mul_of_nonneg_left hend (abs_nonneg (Analysis.combinedZeroWeight T R))
  have hparts := combined_weight_countArg_parts hRH hT hTR
  change
    (∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * zetaArgCount t)) =
      Analysis.combinedZeroWeight T R * P R -
        ∫ t in T..R, Analysis.combinedZeroWeightDeriv T t * P t at hparts
  rw [hparts]
  have htriangle :=
    abs_sub (Analysis.combinedZeroWeight T R * P R)
      (∫ t in T..R, Analysis.combinedZeroWeightDeriv T t * P t)
  rw [abs_mul] at htriangle
  exact htriangle.trans (add_le_add hmul hbound)

/-- Under RH, the finite combined-weight count-argument integral has the
explicit tail budget with coefficient `29 / 27` and the logarithmic
variation constant. The sole additional term is the finite upper-endpoint
contribution, which tends to zero as `R` tends to infinity. -/
theorem combined_weight_countArg_explicit (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    |∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * zetaArgCount t)| ≤
      |Analysis.combinedZeroWeight T R| *
          (16 + (7 / 5 : ℝ) * Real.log T + (7 / 5 : ℝ) * Real.log (R / T)) +
        ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
            (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27)) /
          T ^ 2 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
  have hA : 0 ≤ 16 + (7 / 5 : ℝ) * Real.log T := by linarith only [hlog]
  have hvar :=
    Analysis.combinedZeroWeight_budget_interval (A := 16 + (7 / 5 : ℝ) * Real.log T) (B :=
      (7 / 5 : ℝ)) hT0 hTR hA (by norm_num only)
  have hfinite := combined_weight_countArg_finite_bound hRH hT hTR
  exact hfinite.trans (add_le_add_right hvar _)

/-- For positive `T`, the finite upper-endpoint budget in the combined
weight estimate tends to zero. The weight decays faster than the logarithm. -/
theorem combined_weight_endpoint_tendsto {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto
      (fun R : ℝ ↦
        |Analysis.combinedZeroWeight T R| *
          (16 + (7 / 5 : ℝ) * Real.log T + (7 / 5 : ℝ) * Real.log (R / T)))
      Filter.atTop (nhds 0) := by
  have hw := Analysis.tendsto_combinedZeroWeight T
  have hwl := Analysis.tendsto_combinedZeroWeight_mul_log T
  have h := (hw.const_mul 16).add (hwl.const_mul (7 / 5 : ℝ))
  simp only [mul_zero, add_zero] at h
  have ha := h.abs
  simp only [abs_zero] at ha
  apply ha.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
  have hR0 : 0 < R := by linarith only [hR]
  have hl : 0 ≤ Real.log R := Real.log_nonneg hR
  have hnon : 0 ≤ 16 + (7 / 5 : ℝ) * Real.log R := by linarith only [hl]
  rw [Real.log_div hR0.ne' hT.ne']
  have he :
    16 * Analysis.combinedZeroWeight T R +
        (7 / 5 : ℝ) * (Analysis.combinedZeroWeight T R * Real.log R) =
      Analysis.combinedZeroWeight T R * (16 + (7 / 5 : ℝ) * Real.log R) := by
    ring
  rw [he, abs_mul, abs_of_nonneg hnon]
  congr 1
  ring

/-- Under RH, any limit of the finite combined-weight count-argument
integrals is bounded by the explicit `29 / 27` variation budget. This
isolates the remaining convergence or integrability step for that integral. -/
theorem combined_weight_countArg_limit_bound (hRH : RiemannHypothesis) {T I : ℝ} (hT : 100 ≤ T)
    (hlim :
      Filter.Tendsto
        (fun R : ℝ ↦ ∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * zetaArgCount t))
        Filter.atTop (nhds I)) :
    |I| ≤
      ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
          (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27)) /
        T ^ 2 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hend :=
    (combined_weight_endpoint_tendsto hT0).add_const
      (((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
          (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27)) /
        T ^ 2)
  simp only [zero_add] at hend
  apply le_of_tendsto_of_tendsto hlim.abs hend
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  exact combined_weight_countArg_explicit hRH hT hR

/-- Under RH, the count-argument moving primitive is continuous on the
open half-line above its positive base point. Local interval integrability
allows jumps in the original zero count. -/
theorem countArg_moving_continuousOn (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun t : ℝ ↦ ∫ y in T..t, 2 * zetaArgCount y) (Set.Ioi T) := by
  intro t ht
  change T < t at ht
  have hR : T ≤ t + 1 := by linarith only [ht]
  have hf := (zetaArgCount_integrable hRH hT hR).const_mul 2
  have hP := hf.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  have hcont := hP.continuousOn
  rw [Set.uIcc_of_le hR] at hcont
  have hmem : t ∈ Set.Icc T (t + 1) := ⟨ht.le, by linarith only⟩
  have hn : Set.Icc T (t + 1) ∈ nhds t := Icc_mem_nhds ht (by linarith only)
  exact (hcont t hmem).continuousAt hn |>.continuousWithinAt

/-- Under RH, the derivative of the combined weight times the moving
count-argument primitive is integrable above `T ≥ 100`. Its absolute
value is dominated by the explicitly integrable variation budget. -/
theorem combined_weight_primitive_integrable (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    MeasureTheory.IntegrableOn
      (fun t ↦ Analysis.combinedZeroWeightDeriv T t * (∫ y in T..t, 2 * zetaArgCount y))
      (Set.Ioi T) := by
  have hT0 : 0 < T := by linarith only [hT]
  let P : ℝ → ℝ := fun t ↦ ∫ y in T..t, 2 * zetaArgCount y
  let A : ℝ := 16 + (7 / 5 : ℝ) * Real.log T
  have hmajor := (Analysis.combinedZeroWeight_budget_integral (A := A) (B := (7 / 5 : ℝ)) hT0).1
  have hc : ContinuousOn (fun t ↦ Analysis.combinedZeroWeightDeriv T t * P t) (Set.Ioi T) := by
    intro t ht
    have ht0 : 0 < t := hT0.trans ht
    have hd := Analysis.combinedZeroWeightDeriv_continuousOn (R := t + 1) hT0
    have hmem : t ∈ Set.Icc T (t + 1) := ⟨ht.le, by linarith only⟩
    have hn : Set.Icc T (t + 1) ∈ nhds t := Icc_mem_nhds ht (by linarith only)
    have hdc := (hd t hmem).continuousAt hn
    have hpc := countArg_moving_continuousOn hRH hT0 t ht
    exact (hdc.continuousWithinAt.mul hpc)
  apply hmajor.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have hp := countArg_moving_integral_bound hRH hT ht.le
  change |P t| ≤ A + (7 / 5 : ℝ) * Real.log (t / T) at hp
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)

/-- Under RH, the finite combined-weight count-argument integrals converge
as the upper endpoint tends to infinity. Integration by parts expresses the
limit through an absolutely integrable weighted moving primitive; the
upper-endpoint contribution tends to zero. -/
theorem combined_weight_countArg_tendsto (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    Filter.Tendsto (fun R : ℝ ↦ ∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * zetaArgCount t))
      Filter.atTop
      (nhds
        (-(∫ t in Set.Ioi T,
            Analysis.combinedZeroWeightDeriv T t * (∫ y in T..t, 2 * zetaArgCount y)))) := by
  have hT0 : 0 < T := by linarith only [hT]
  let P : ℝ → ℝ := fun t ↦ ∫ y in T..t, 2 * zetaArgCount y
  have hend :
    Filter.Tendsto (fun R : ℝ ↦ Analysis.combinedZeroWeight T R * P R) Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _ (combined_weight_endpoint_tendsto hT0)
    filter_upwards [Filter.eventually_ge_atTop T] with R hR
    have hp := countArg_moving_integral_bound hRH hT hR
    change |P R| ≤ 16 + (7 / 5 : ℝ) * Real.log T + (7 / 5 : ℝ) * Real.log (R / T) at hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  have hi := combined_weight_primitive_integrable hRH hT
  have hlim :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi T hi
      (Filter.tendsto_id : Filter.Tendsto (fun x : ℝ ↦ x) Filter.atTop Filter.atTop)
  have h := hend.sub hlim
  simp only [zero_sub] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  exact (combined_weight_countArg_parts hRH hT hR).symm

/-- Under RH, the limit of the finite combined-weight count-argument
integrals exists and satisfies the explicit `29 / 27` logarithmic budget.
The limit is represented by the integrable weighted moving primitive. -/
theorem combined_weight_countArg_infinite_bound (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    |∫ t in Set.Ioi T, Analysis.combinedZeroWeightDeriv T t * (∫ y in T..t, 2 * zetaArgCount y)| ≤
      ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
          (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27)) /
        T ^ 2 := by
  have h := combined_weight_countArg_limit_bound hRH hT (combined_weight_countArg_tendsto hRH hT)
  simpa only [abs_neg] using h

/-- At heights above `T ≥ 100`, the Gamma-phase contribution weighted by
the combined zero kernel is integrable and has absolute integral at most
`1 / (10 T²)`. The sign change at `2T` is retained in the exact kernel
integral. -/
theorem combined_weight_theta_bound {T : ℝ} (hT : 100 ≤ T) :
    MeasureTheory.IntegrableOn
        (fun t ↦ Analysis.combinedZeroWeight T t * (2 * backlundThetaError t)) (Set.Ioi T) ∧
      |∫ t in Set.Ioi T, Analysis.combinedZeroWeight T t * (2 * backlundThetaError t)| ≤
        1 / (10 * T ^ 2) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hc :
    ContinuousOn (fun t ↦ Analysis.combinedZeroWeight T t * (2 * backlundThetaError t))
      (Set.Ioi T) := by
    intro t ht
    have ht0 : 0 < t := hT0.trans ht
    exact
      ((Analysis.combinedZeroWeight_continuousAt ht0.ne').mul
          (continuousAt_const.mul (continuousAt_backlundThetaError ht0))).continuousWithinAt
  have hmajor :
    MeasureTheory.IntegrableOn (fun t ↦ (2 / 5 : ℝ) * |Analysis.combinedGammaWeight T t|)
      (Set.Ioi T) :=
    (Analysis.combinedGammaWeight_integrable hT0).const_mul (2 / 5 : ℝ)
  have hbound :
    ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi T)),
      ‖Analysis.combinedZeroWeight T t * (2 * backlundThetaError t)‖ ≤
        (2 / 5 : ℝ) * |Analysis.combinedGammaWeight T t| := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := hT0.trans ht
    have htheta := thetaError_twice_le (le_trans hT ht.le)
    have hm := mul_le_mul_of_nonneg_left htheta (abs_nonneg (Analysis.combinedZeroWeight T t))
    rw [Real.norm_eq_abs, abs_mul]
    have he :
      |Analysis.combinedZeroWeight T t| * (2 / (5 * t)) =
        (2 / 5 : ℝ) * (|Analysis.combinedZeroWeight T t| / t) := by
      ring
    rw [he, Analysis.abs_combinedZeroWeight_div ht0] at hm
    exact hm
  have hi := hmajor.mono' (hc.aestronglyMeasurable measurableSet_Ioi) hbound
  refine ⟨hi, ?_⟩
  have hint :=
    MeasureTheory.integral_mono_ae hi.abs hmajor
      (by
        filter_upwards [hbound] with t ht
        simpa only [Real.norm_eq_abs] using ht)
  have hnorm :=
    MeasureTheory.abs_integral_le_integral_abs (μ := MeasureTheory.volume.restrict (Set.Ioi T))
      (f := fun t ↦ Analysis.combinedZeroWeight T t * (2 * backlundThetaError t))
  rw [MeasureTheory.integral_const_mul, Analysis.combinedGammaWeight_integral hT0] at hint
  have he : (2 / 5 : ℝ) * (1 / (4 * T ^ 2)) = 1 / (10 * T ^ 2) := by ring
  rw [he] at hint
  exact hnorm.trans hint

/-- Under RH, the finite weighted zero-count error integral splits into
the count-argument term and the Gamma-phase term. The decomposition holds
also at zero ordinates under the closed counting convention. -/
theorem combined_weight_error_split (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    (∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCountError t) =
      (∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * zetaArgCount t)) +
        ∫ t in T..R, Analysis.combinedZeroWeight T t * (2 * backlundThetaError t) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hw := (Analysis.combinedZeroWeight_absContinuous hT0 hTR).continuousOn
  have ha :
    IntervalIntegrable (fun t ↦ Analysis.combinedZeroWeight T t * (2 * zetaArgCount t))
      MeasureTheory.volume T R :=
    ((zetaArgCount_integrable hRH hT0 hTR).const_mul 2).continuousOn_mul hw
  have hg :
    IntervalIntegrable (fun t ↦ Analysis.combinedZeroWeight T t * (2 * backlundThetaError t))
      MeasureTheory.volume T R := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hTR).mpr
    exact (combined_weight_theta_bound hT).1.mono_set Set.Ioc_subset_Ioi_self
  rw [← intervalIntegral.integral_add ha hg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hTR] at ht
  change
    Analysis.combinedZeroWeight T t * zeroCountError t =
      Analysis.combinedZeroWeight T t * (2 * zetaArgCount t) +
        Analysis.combinedZeroWeight T t * (2 * backlundThetaError t)
  rw [zeroCountError_eq_arg hRH (hT0.trans_le ht.1), mul_add]

/-- Under RH, the finite combined-weight zero-count error integrals
converge to an explicit sum of the moving-primitive and Gamma contributions.
Both components are internally integrable on the positive tail. -/
theorem combined_weight_error_tendsto (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    Filter.Tendsto (fun R : ℝ ↦ ∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCountError t)
      Filter.atTop
      (nhds
        (-(∫ t in Set.Ioi T,
              Analysis.combinedZeroWeightDeriv T t * (∫ y in T..t, 2 * zetaArgCount y)) +
          ∫ t in Set.Ioi T, Analysis.combinedZeroWeight T t * (2 * backlundThetaError t))) := by
  have ha := combined_weight_countArg_tendsto hRH hT
  have hg :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi T (combined_weight_theta_bound hT).1
      (Filter.tendsto_id : Filter.Tendsto (fun x : ℝ ↦ x) Filter.atTop Filter.atTop)
  have h := ha.add hg
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  exact (combined_weight_error_split hRH hT hR).symm

/-- Under RH, the limit of the combined-weight zero-count error integral
has the explicit remainder budget from the integrated zero-count plan.
The count-argument and Gamma-phase bounds are proved separately. -/
theorem combined_weight_error_limit_bound (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    |-(∫ t in Set.Ioi T, Analysis.combinedZeroWeightDeriv T t * (∫ y in T..t, 2 * zetaArgCount y)) +
          ∫ t in Set.Ioi T, Analysis.combinedZeroWeight T t * (2 * backlundThetaError t)| ≤
      ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
          (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
          1 / 10) /
        T ^ 2 := by
  have harg := combined_weight_countArg_infinite_bound hRH hT
  have hgamma := (combined_weight_theta_bound hT).2
  have htri :=
    abs_add_le
      (-(∫ t in Set.Ioi T,
          Analysis.combinedZeroWeightDeriv T t * (∫ y in T..t, 2 * zetaArgCount y)))
      (∫ t in Set.Ioi T, Analysis.combinedZeroWeight T t * (2 * backlundThetaError t))
  rw [abs_neg] at htri
  simp only [div_eq_mul_inv, mul_inv_rev] at harg hgamma ⊢
  nlinarith only [htri, harg, hgamma]

/-- Under RH, the improper combined-weight zero-count error integral
exists as the limit of its finite interval integrals and has the explicit
remainder bound for every `T ≥ 100`. No zero table or external count-error
hypothesis is used. -/
theorem combined_weight_error_remainder (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    ∃ I : ℝ,
      Filter.Tendsto (fun R : ℝ ↦ ∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCountError t)
          Filter.atTop (nhds I) ∧
        |I| ≤
          ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
              (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
              1 / 10) /
            T ^ 2 := by
  exact ⟨_, combined_weight_error_tendsto hRH hT, combined_weight_error_limit_bound hRH hT⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
