/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedAbelRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountArgumentIntegralRH
import PseudoPrime.Analysis.MovingPrimitiveParts
import PseudoPrime.Analysis.LogBudgetIntegral
import PseudoPrime.Analysis.LogPowerTailIntegral
import PseudoPrime.Analysis.LogLinearIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountInverseSquare
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Inverse-square integrals of the zero-count error -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the closed-endpoint zero-count error is interval integrable
on every ordered interval starting at least at 100. Its count-argument
component is integrable and its Gamma-phase component is continuous. -/
theorem zeroCountError_intervalIntegrable (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) : IntervalIntegrable zeroCountError MeasureTheory.volume T R := by
  have hT0 : 0 < T := by linarith only [hT]
  have harg := (zetaArgCount_integrable hRH hT0 hTR).const_mul 2
  have htheta : IntervalIntegrable (fun t ↦ 2 * backlundThetaError t) MeasureTheory.volume T R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTR
    intro t ht
    exact
      (continuousAt_const.mul
          (continuousAt_backlundThetaError (hT0.trans_le ht.1))).continuousWithinAt
  have hsum := harg.add htheta
  apply hsum.congr
  intro t ht
  rw [Set.uIoc_of_le hTR] at ht
  exact (zeroCountError_eq_arg hRH (hT0.trans ht.1)).symm

/-- Under RH, the moving primitive of the full zero-count error has a
scale-separated logarithmic bound. The coefficient `9 / 5` includes both
the argument and Gamma-phase contributions. -/
theorem zeroCountError_moving_bound (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    |∫ t in T..R, zeroCountError t| ≤
      16 + (7 / 5 : ℝ) * Real.log T + (9 / 5 : ℝ) * Real.log (R / T) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hR0 : 0 < R := hT0.trans_le hTR
  have h := countError_integral_bound hRH hT hTR
  have hlog : Real.log (R / T) = Real.log R - Real.log T := Real.log_div hR0.ne' hT0.ne'
  rw [hlog] at h ⊢
  linarith only [h]

/-- Under RH, the inverse-square weighted zero-count error on a finite
interval equals an upper-endpoint term and the moving-primitive integral.
The integration by parts is valid even at zero ordinates. -/
theorem zeroCountError_invSq_parts (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    (∫ t in T..R, t⁻¹ ^ 2 * zeroCountError t) =
      R⁻¹ ^ 2 * (∫ y in T..R, zeroCountError y) -
        ∫ t in T..R, (-2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hf := zeroCountError_intervalIntegrable hRH hT hTR
  have hw : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t⁻¹ ^ 2) T R := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [Set.uIcc_of_le hTR]
    exact (contDiffOn_id.inv (fun t ht ↦ (hT0.trans_le ht.1).ne')).pow 2
  apply Analysis.integral_mul_of_moving_primitive hTR hf hw
  intro t ht
  have ht0 : t ≠ 0 := (hT0.trans_le ht.1).ne'
  have h := (hasDerivAt_inv ht0).pow 2
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, ← inv_pow] at h
  convert h using 1
  ring

/-- For positive `T ≤ R` and nonnegative `A, B`, the inverse-cube
integral of the scale-separated logarithmic budget is at most its full
tail value `(A + B / 2) / T²`. The explicit primitive has a nonnegative
upper-endpoint term. -/
theorem invCube_log_budget_interval {T R A B : ℝ} (hT : 0 < T) (hTR : T ≤ R) (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    (∫ t in T..R, (A + B * Real.log (t / T)) * (2 * t⁻¹ ^ 3)) ≤ (A + B / 2) / T ^ 2 := by
  have hR : 0 < R := hT.trans_le hTR
  have hlogR : 0 ≤ Real.log (R / T) := Real.log_nonneg ((one_le_div hT).2 hTR)
  have he :
    (∫ t in T..R, (A + B * Real.log (t / T)) * (2 * t⁻¹ ^ 3)) =
      ∫ t in T..R, (B * Real.log t + (A - B * Real.log T) + 0 / t) * (2 * t⁻¹ ^ 3) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hTR] at ht
    have ht0 : 0 < t := hT.trans_le ht.1
    change
      (A + B * Real.log (t / T)) * (2 * t⁻¹ ^ 3) =
        (B * Real.log t + (A - B * Real.log T) + 0 / t) * (2 * t⁻¹ ^ 3)
    rw [Real.log_div ht0.ne' hT.ne', zero_div, add_zero]
    ring
  have hi :=
    Analysis.integral_log_budget_inv_cube (a := T) (b := R) (α := B) (β := A - B * Real.log T) (γ :=
      0) hT hTR
  rw [he, hi]
  have hRnum : 0 ≤ B * (Real.log R + 1 / 2) + (A - B * Real.log T) := by
    have hlog : Real.log (R / T) = Real.log R - Real.log T := Real.log_div hR.ne' hT.ne'
    have hm := mul_nonneg hB hlogR
    nlinarith only [hm, hlog, hA, hB]
  have hRterm : 0 ≤ (B * (Real.log R + 1 / 2) + (A - B * Real.log T)) / R ^ 2 :=
    div_nonneg hRnum (sq_nonneg R)
  norm_num only
  simp only [div_eq_mul_inv] at hRterm ⊢
  nlinarith only [hRterm]

/-- For `T ≥ 1`, an affine logarithmic budget times the inverse-cube
kernel is integrable on the upper half-line. Logarithmic power-tail
integrability supplies both terms. -/
theorem invCube_log_budget_integrable {T A B : ℝ} (hT : 1 ≤ T) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ (A + B * Real.log (t / T)) * (2 * t⁻¹ ^ 3))
      (Set.Ioi T) := by
  have hlog0 := Analysis.log_power_tail_integrable (r := (2 : ℝ)) (a := T) (by norm_num only) hT 1
  have hinv0 := Analysis.log_power_tail_integrable (r := (2 : ℝ)) (a := T) (by norm_num only) hT 0
  have hlog : MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t * t⁻¹ ^ 3) (Set.Ioi T) := by
    apply hlog0.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := zero_le_one.trans (hT.trans ht.le)
    have hr : t ^ (-(2 : ℝ) - 1) = t⁻¹ ^ 3 := by
      have he : (-(2 : ℝ) - 1) = -(3 : ℝ) := by ring
      rw [he, Real.rpow_neg ht0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast, ←
        inv_pow]
    simp only [pow_one, hr]
  have hinv : MeasureTheory.IntegrableOn (fun t : ℝ ↦ t⁻¹ ^ 3) (Set.Ioi T) := by
    apply hinv0.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := zero_le_one.trans (hT.trans ht.le)
    have hr : t ^ (-(2 : ℝ) - 1) = t⁻¹ ^ 3 := by
      have he : (-(2 : ℝ) - 1) = -(3 : ℝ) := by ring
      rw [he, Real.rpow_neg ht0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast, ←
        inv_pow]
    simp only [pow_zero, one_mul, hr]
  have hi := (hinv.const_mul (2 * (A - B * Real.log T))).add (hlog.const_mul (2 * B))
  apply hi.congr
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := zero_lt_one.trans_le (hT.trans ht.le)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  rw [Real.log_div ht0.ne' hT0.ne']
  dsimp only [Pi.add_apply]
  ring

/-- Under RH, the finite inverse-square weighted count-error integral is
bounded by the moving-primitive endpoint and the explicit inverse-cube
budget. This estimate keeps the lower endpoint fixed at `T ≥ 100`. -/
theorem zeroCountError_invSq_finite_bound (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    |∫ t in T..R, t⁻¹ ^ 2 * zeroCountError t| ≤
      R⁻¹ ^ 2 * (16 + (7 / 5 : ℝ) * Real.log T + (9 / 5 : ℝ) * Real.log (R / T)) +
        (16 + (7 / 5 : ℝ) * Real.log T + 9 / 10) / T ^ 2 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hR0 : 0 < R := hT0.trans_le hTR
  let P : ℝ → ℝ := fun t ↦ ∫ y in T..t, zeroCountError y
  let A : ℝ := 16 + (7 / 5 : ℝ) * Real.log T
  let B : ℝ → ℝ := fun t ↦ A + (9 / 5 : ℝ) * Real.log (t / T)
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hl : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
    linarith only [hl]
  have hf := zeroCountError_intervalIntegrable hRH hT hTR
  have hP : AbsolutelyContinuousOnInterval P T R :=
    hf.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  have hk : ContinuousOn (fun t : ℝ ↦ -2 * t⁻¹ ^ 3) (Set.uIcc T R) := by
    rw [Set.uIcc_of_le hTR]
    intro t ht
    have h : ContinuousAt (fun x : ℝ ↦ -2 * x⁻¹ ^ 3) t :=
      continuousAt_const.mul ((continuousAt_id.inv₀ (hT0.trans_le ht.1).ne').pow 3)
    exact h.continuousWithinAt
  have hi : IntervalIntegrable (fun t ↦ (-2 * t⁻¹ ^ 3) * P t) MeasureTheory.volume T R :=
    (hk.intervalIntegrable).mul_continuousOn hP.continuousOn
  have hB : ContinuousOn B (Set.uIcc T R) := by
    rw [Set.uIcc_of_le hTR]
    intro t ht
    have hlog : ContinuousAt (fun x : ℝ ↦ Real.log (x / T)) t :=
      ContinuousAt.comp (f := fun x : ℝ ↦ x / T)
        (Real.continuousAt_log (div_ne_zero (hT0.trans_le ht.1).ne' hT0.ne'))
        (continuousAt_id.div_const T)
    exact (continuousAt_const.add (continuousAt_const.mul hlog)).continuousWithinAt
  have hmaj : IntervalIntegrable (fun t ↦ B t * (2 * t⁻¹ ^ 3)) MeasureTheory.volume T R := by
    apply ContinuousOn.intervalIntegrable
    apply hB.mul
    rw [Set.uIcc_of_le hTR]
    intro t ht
    have h : ContinuousAt (fun x : ℝ ↦ 2 * x⁻¹ ^ 3) t :=
      continuousAt_const.mul ((continuousAt_id.inv₀ (hT0.trans_le ht.1).ne').pow 3)
    exact h.continuousWithinAt
  have hpoint : ∀ t ∈ Set.Icc T R, ‖(-2 * t⁻¹ ^ 3) * P t‖ ≤ B t * (2 * t⁻¹ ^ 3) := by
    intro t ht
    have ht0 : 0 < t := hT0.trans_le ht.1
    have hp := zeroCountError_moving_bound hRH hT ht.1
    change |P t| ≤ B t at hp
    have hk0 : 0 ≤ 2 * t⁻¹ ^ 3 :=
      mul_nonneg (by norm_num only) (pow_nonneg (inv_nonneg.mpr ht0.le) 3)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos (by nlinarith only [hk0] : -2 * t⁻¹ ^ 3 ≤ 0)]
    have hm := mul_le_mul_of_nonneg_right hp hk0
    nlinarith only [hm]
  have hint := intervalIntegral.integral_mono_on hTR hi.norm hmaj hpoint
  have hnorm :=
    intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := fun t ↦
      (-2 * t⁻¹ ^ 3) * P t) hTR
  rw [Real.norm_eq_abs] at hnorm
  have hbudget := invCube_log_budget_interval hT0 hTR hA (by norm_num only : (0 : ℝ) ≤ 9 / 5)
  change (∫ t in T..R, B t * (2 * t⁻¹ ^ 3)) ≤ (A + (9 / 5 : ℝ) / 2) / T ^ 2 at hbudget
  have hcorr : |∫ t in T..R, (-2 * t⁻¹ ^ 3) * P t| ≤ (A + (9 / 5 : ℝ) / 2) / T ^ 2 :=
    (hnorm.trans hint).trans hbudget
  have hpR := zeroCountError_moving_bound hRH hT hTR
  change |P R| ≤ B R at hpR
  have hend := mul_le_mul_of_nonneg_left hpR (sq_nonneg R⁻¹)
  have hparts := zeroCountError_invSq_parts hRH hT hTR
  change
    (∫ t in T..R, t⁻¹ ^ 2 * zeroCountError t) =
      R⁻¹ ^ 2 * P R - ∫ t in T..R, (-2 * t⁻¹ ^ 3) * P t at hparts
  rw [hparts]
  have htri := abs_sub (R⁻¹ ^ 2 * P R) (∫ t in T..R, (-2 * t⁻¹ ^ 3) * P t)
  rw [abs_mul, abs_of_nonneg (sq_nonneg R⁻¹)] at htri
  dsimp only [A, B] at hend hcorr
  nlinarith only [htri, hend, hcorr]

/-- Under RH, the moving primitive of the zero-count error is continuous
above every base height at least 100, despite jumps in the count itself. -/
theorem zeroCountError_moving_continuousOn (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    ContinuousOn (fun t : ℝ ↦ ∫ y in T..t, zeroCountError y) (Set.Ioi T) := by
  intro t ht
  change T < t at ht
  have hR : T ≤ t + 1 := by linarith only [ht]
  have hf := zeroCountError_intervalIntegrable hRH hT hR
  have hP := hf.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc
  have hcont := hP.continuousOn
  rw [Set.uIcc_of_le hR] at hcont
  have hmem : t ∈ Set.Icc T (t + 1) := ⟨ht.le, by linarith only⟩
  have hn : Set.Icc T (t + 1) ∈ nhds t := Icc_mem_nhds ht (by linarith only)
  exact (hcont t hmem).continuousAt hn |>.continuousWithinAt

/-- Under RH, the inverse-cube weighted moving primitive of the zero-count
error is integrable above `T ≥ 100`. The explicit logarithmic budget is an
integrable pointwise majorant. -/
theorem zeroCountError_primitive_integrable (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    MeasureTheory.IntegrableOn (fun t ↦ (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y))
      (Set.Ioi T) := by
  have hT0 : 0 < T := by linarith only [hT]
  let P : ℝ → ℝ := fun t ↦ ∫ y in T..t, zeroCountError y
  let A : ℝ := 16 + (7 / 5 : ℝ) * Real.log T
  have hmajor :=
    invCube_log_budget_integrable (A := A) (B := (9 / 5 : ℝ)) (T := T) (by linarith only [hT])
  have hc : ContinuousOn (fun t ↦ (2 * t⁻¹ ^ 3) * P t) (Set.Ioi T) := by
    intro t ht
    have ht0 : 0 < t := hT0.trans ht
    have hp := zeroCountError_moving_continuousOn hRH hT t ht
    exact (continuousAt_const.mul ((continuousAt_id.inv₀ ht0.ne').pow 3)).continuousWithinAt.mul hp
  apply hmajor.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := hT0.trans ht
  have hp := zeroCountError_moving_bound hRH hT ht.le
  change |P t| ≤ A + (9 / 5 : ℝ) * Real.log (t / T) at hp
  have hk : 0 ≤ 2 * t⁻¹ ^ 3 := mul_nonneg (by norm_num only) (pow_nonneg (inv_nonneg.mpr ht0.le) 3)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk]
  exact (mul_le_mul_of_nonneg_left hp hk).trans_eq (mul_comm _ _)

/-- Under RH, the upper boundary term of the inverse-square integration
by parts tends to zero. The moving primitive grows at most logarithmically. -/
theorem zeroCountError_invSq_endpoint_tendsto (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    Filter.Tendsto (fun R : ℝ ↦ R⁻¹ ^ 2 * (∫ y in T..R, zeroCountError y)) Filter.atTop
      (nhds 0) := by
  have hT0 : 0 < T := by linarith only [hT]
  have hlog2 : Filter.Tendsto (fun R : ℝ ↦ Real.log R / R ^ 2) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (2 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] using h
  have hi : Filter.Tendsto (fun R : ℝ ↦ R⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hmajor := ((hi.pow 2).const_mul 16).add (hlog2.const_mul (9 / 5 : ℝ))
  norm_num only at hmajor
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  have hR0 : 0 < R := hT0.trans_le hR
  have hp := zeroCountError_moving_bound hRH hT hR
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
  have hlog : Real.log (R / T) = Real.log R - Real.log T := Real.log_div hR0.ne' hT0.ne'
  rw [hlog] at hp
  have hp' : |∫ y in T..R, zeroCountError y| ≤ 16 + (9 / 5 : ℝ) * Real.log R := by
    linarith only [hp, hlogT]
  have hm := mul_le_mul_of_nonneg_left hp' (sq_nonneg R⁻¹)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg R⁻¹)]
  convert hm using 1
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- For positive `T`, the logarithmic upper-endpoint budget divided by
`R²` tends to zero as `R` tends to infinity. -/
theorem invSq_log_budget_endpoint_tendsto {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto
      (fun R : ℝ ↦ R⁻¹ ^ 2 * (16 + (7 / 5 : ℝ) * Real.log T + (9 / 5 : ℝ) * Real.log (R / T)))
      Filter.atTop (nhds 0) := by
  have hlog2 : Filter.Tendsto (fun R : ℝ ↦ Real.log R / R ^ 2) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (2 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] using h
  have hi : Filter.Tendsto (fun R : ℝ ↦ R⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := ((hi.pow 2).const_mul (16 - (2 / 5 : ℝ) * Real.log T)).add (hlog2.const_mul (9 / 5 : ℝ))
  norm_num only at h
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.log_div hR.ne' hT.ne']
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- Under RH, the inverse-square weighted zero-count error has a finite
improper integral. Its value is the integral of the inverse-cube weighted
moving primitive, which is absolutely integrable. -/
theorem zeroCountError_invSq_tendsto (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    Filter.Tendsto (fun R : ℝ ↦ ∫ t in T..R, t⁻¹ ^ 2 * zeroCountError t) Filter.atTop
      (nhds (∫ t in Set.Ioi T, (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y))) := by
  have hend := zeroCountError_invSq_endpoint_tendsto hRH hT
  have hi := zeroCountError_primitive_integrable hRH hT
  have hlim :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi T hi
      (Filter.tendsto_id : Filter.Tendsto (fun x : ℝ ↦ x) Filter.atTop Filter.atTop)
  have h := hend.add hlim
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  have hp := zeroCountError_invSq_parts hRH hT hR
  have he :
    (∫ t in T..R, (-2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y)) =
      -(∫ t in T..R, (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    change
      (-2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y) =
        -((2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y))
    ring
  rw [he] at hp
  simpa only [id_eq, sub_neg_eq_add] using hp.symm

/-- Under RH and `T ≥ 100`, the inverse-square error integral represented
by its absolutely integrable moving primitive is bounded by
`(16 + (7/5) log T + 9/10) / T²`. -/
theorem zeroCountError_invSq_infinite_bound (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    |∫ t in Set.Ioi T, (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y)| ≤
      (16 + (7 / 5 : ℝ) * Real.log T + 9 / 10) / T ^ 2 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hend :=
    (invSq_log_budget_endpoint_tendsto hT0).add_const
      ((16 + (7 / 5 : ℝ) * Real.log T + 9 / 10) / T ^ 2)
  simp only [zero_add] at hend
  apply le_of_tendsto_of_tendsto (zeroCountError_invSq_tendsto hRH hT).abs hend
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  exact zeroCountError_invSq_finite_bound hRH hT hR

/-- For `100 ≤ T ≤ R`, the centered reciprocal zero sum changes by the
inverse-square integral of the count error plus its two exact endpoint
terms. The main zero-count contribution cancels analytically. -/
theorem zeroReciprocal_centered_finite (hRH : RiemannHypothesis) {T R : ℝ} (hT : 100 ≤ T)
    (hTR : T ≤ R) :
    zeroReciprocalSum R - (Real.log R - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) =
      zeroReciprocalSum T - (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) -
          zeroCountError T / T +
        zeroCountError R / R +
        ∫ t in T..R, t⁻¹ ^ 2 * zeroCountError t := by
  have hT0 : 0 < T := by linarith only [hT]
  let M : ℝ → ℝ := fun t ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4
  have hM : ContinuousOn M (Set.uIcc T R) := by
    rw [Set.uIcc_of_le hTR]
    intro t ht
    have ht0 : t ≠ 0 := (hT0.trans_le ht.1).ne'
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hk : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc T R) := by
    rw [Set.uIcc_of_le hTR]
    intro t ht
    exact ((continuousAt_id.inv₀ (hT0.trans_le ht.1).ne').pow 2).continuousWithinAt
  have hm : IntervalIntegrable (fun t ↦ M t / t ^ 2) MeasureTheory.volume T R := by
    have h : IntervalIntegrable (fun t ↦ M t * t⁻¹ ^ 2) MeasureTheory.volume T R :=
      (hM.mul hk).intervalIntegrable
    convert h using 1
    funext t
    simp only [div_eq_mul_inv, ← inv_pow]
  have hq : IntervalIntegrable (fun t ↦ t⁻¹ ^ 2 * zeroCountError t) MeasureTheory.volume T R :=
    (zeroCountError_intervalIntegrable hRH hT hTR).continuousOn_mul hk
  have heq :
    (∫ t in T..R, zeroCount t / t ^ 2) =
      (∫ t in T..R, M t / t ^ 2) + ∫ t in T..R, t⁻¹ ^ 2 * zeroCountError t := by
    rw [← intervalIntegral.integral_add hm hq]
    apply intervalIntegral.integral_congr
    intro t ht
    change zeroCount t / t ^ 2 = M t / t ^ 2 + t⁻¹ ^ 2 * (zeroCount t - M t)
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  have hs := zeroReciprocal_abel (by linarith only [hT] : 1 < T) hTR
  rw [heq] at hs
  have hmval :=
    Analysis.log_linear_div_sq_boundary (a := T) (b := R) (k := 1 / Real.pi) (c :=
      Real.log (2 * Real.pi)) (d := 7 / 4) hT0 hTR
  change M R / R + (∫ t in T..R, M t / t ^ 2) = _ at hmval
  have hcancel :
    M T / T = (1 / Real.pi) * (Real.log T - Real.log (2 * Real.pi) - 1) + (7 / 4 : ℝ) / T := by
    have hc := mul_inv_cancel₀ hT0.ne'
    dsimp only [M]
    simp only [div_eq_mul_inv]
    linear_combination ((1 / Real.pi) * (Real.log T - Real.log (2 * Real.pi) - 1)) * hc
  have hQT : zeroCountError T = zeroCount T - M T := rfl
  have hQR : zeroCountError R = zeroCount R - M R := rfl
  rw [hQT, hQR]
  simp only [div_eq_mul_inv, mul_inv_rev] at hs hmval hcancel ⊢
  nlinarith only [hs, hmval, hcancel]

/-- Under RH and for `T ≥ 100`, the reciprocal-sum limiting constant is
the finite reciprocal sum minus its quadratic main term and its exact
count-error endpoint, plus the inverse-square count-error tail. The latter
is represented by an absolutely integrable moving primitive. -/
theorem zeroReciprocalConstant_anchor (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalConstant =
      zeroReciprocalSum T - (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) -
          zeroCountError T / T +
        ∫ t in Set.Ioi T, (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y) := by
  have hend :=
    (zeroCountError_div_tendsto hRH).const_add
      (zeroReciprocalSum T - (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) -
        zeroCountError T / T)
  simp only [add_zero] at hend
  have hlim := hend.add (zeroCountError_invSq_tendsto hRH hT)
  apply tendsto_nhds_unique (zeroReciprocalConstant_tendsto hRH)
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop T] with R hR
  exact (zeroReciprocal_centered_finite hRH hT hR).symm

/-- Under RH and `T ≥ 100`, the reciprocal-sum limiting constant lies
within the explicit inverse-square tail budget of its signed finite
anchor. The count at `T` is retained exactly. -/
theorem zeroReciprocalConstant_anchor_error (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    |zeroReciprocalConstant -
          (zeroReciprocalSum T - (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) -
            zeroCountError T / T)| ≤
      (16 + (7 / 5 : ℝ) * Real.log T + 9 / 10) / T ^ 2 := by
  rw [zeroReciprocalConstant_anchor hRH hT]
  have he :
    zeroReciprocalSum T - (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) -
            zeroCountError T / T +
          (∫ t in Set.Ioi T, (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y)) -
        (zeroReciprocalSum T - (Real.log T - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) -
          zeroCountError T / T) =
      ∫ t in Set.Ioi T, (2 * t⁻¹ ^ 3) * (∫ y in T..t, zeroCountError y) := by
    ring
  rw [he]
  exact zeroCountError_invSq_infinite_bound hRH hT

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
