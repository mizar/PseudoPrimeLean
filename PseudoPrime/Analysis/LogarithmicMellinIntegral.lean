/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! # Euler constant in the reciprocal-logarithmic Mellin integral -/

public section

namespace PseudoPrime.Analysis

/-- For exponent `s>1`, the reciprocal-logarithmic Mellin kernel is integrable above two.
Bound it by a constant multiple of the integrable power `t^(-s)`. -/
theorem integrable_logMellin_Ioi {s : ℝ} (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ (-s) / Real.log t) (Set.Ioi 2) := by
  have hbase :=
    (integrableOn_Ioi_rpow_of_lt (by linarith only [hs] : -s < -1)
          (by norm_num only : (0 : ℝ) < 2)).const_mul
      (1 / Real.log 2)
  apply
    MeasureTheory.Integrable.mono' hbase
      (((measurable_id.pow_const (-s)).div Real.measurable_log).aestronglyMeasurable)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans ht
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only)
  have hl : 0 < Real.log t := Real.log_pos ((by norm_num only : (1 : ℝ) < 2).trans ht)
  change ‖t ^ (-s) / Real.log t‖ ≤ (1 / Real.log 2) * t ^ (-s)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg ht0.le _), abs_of_pos hl]
  have h :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le (-s)) hl2
      (Real.log_le_log (by norm_num only : (0 : ℝ) < 2) ht.le)
  convert h using 1
  ring

/-- For `t>1`, differentiate `log(log t) t^(1-s)` and identify its derivative with
the reciprocal-logarithmic kernel minus the logarithmic moment term. -/
theorem logLogMellin_hasDerivAt {s t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ Real.log (Real.log t) * t ^ (1 - s))
      (t ^ (-s) / Real.log t - (s - 1) * (Real.log (Real.log t) * t ^ (-s))) t := by
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hl := (Real.hasDerivAt_log (Real.log_pos ht).ne').comp t (Real.hasDerivAt_log ht0.ne')
  have hp := Real.hasDerivAt_rpow_const (p := 1 - s) (Or.inl ht0.ne')
  have hd := hl.mul hp
  have hpow : t ^ (1 - s) / t = t ^ (-s) := by
    have h := Real.rpow_sub ht0 (1 - s) 1
    rw [Real.rpow_one] at h
    convert h.symm using 1
    congr 1
    ring
  convert hd using 1
  · rfl
  · dsimp only [Function.comp_apply]
    rw [show 1 - s - 1 = -s by ring, ← hpow]
    field_simp (disch :=
      first
      | exact ht0.ne'
      | exact (Real.log_pos ht).ne')
    ring

/-- For `s>1`, the logarithmic moment primitive tends to zero at infinity.
Squeeze it by `log t / t^(s-1)` on a sufficiently large tail. -/
theorem tendsto_logLogMellin_atTop {s : ℝ} (hs : 1 < s) :
    Filter.Tendsto (fun t : ℝ ↦ Real.log (Real.log t) * t ^ (1 - s)) Filter.atTop (nhds 0) := by
  have hlim := (isLittleO_log_rpow_atTop (sub_pos.mpr hs)).tendsto_div_nhds_zero
  apply squeeze_zero' ?_ ?_ hlim
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp (1 : ℝ))] with t ht
    have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
    have hl : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ht
    exact mul_nonneg (Real.log_nonneg hl) (Real.rpow_nonneg ht0.le _)
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp (1 : ℝ))] with t ht
    have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
    have hl : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ht
    have hll : Real.log (Real.log t) ≤ Real.log t := by
      have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hl)
      linarith only [h]
    rw [show 1 - s = -(s - 1) by ring, Real.rpow_neg ht0.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hll (Real.rpow_nonneg ht0.le _)

/-- For `s>1`, integration by parts expresses the reciprocal-logarithmic Mellin
integral above two using the log-log moment and the exact lower endpoint. -/
theorem logMellin_eq_logLog_integral {s : ℝ} (hs : 1 < s) :
    (∫ t : ℝ in Set.Ioi 2, t ^ (-s) / Real.log t) =
      (s - 1) * (∫ t : ℝ in Set.Ioi 2, Real.log (Real.log t) * t ^ (-s)) -
        Real.log (Real.log 2) * (2 : ℝ) ^ (1 - s) := by
  have hJ := integrable_logMellin_Ioi hs
  have hH :=
    (Real.integrableOn_log_log_mul_rpow hs).mono_set
      (fun t ht ↦ (by norm_num only : (1 : ℝ) < 2).trans ht)
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun t ht ↦ logLogMellin_hasDerivAt ((by norm_num only : (1 : ℝ) < 2).trans_le ht))
      (hJ.sub (hH.const_mul (s - 1))) (tendsto_logLogMellin_atTop hs)
  rw [MeasureTheory.integral_sub hJ (hH.const_mul (s - 1)), MeasureTheory.integral_const_mul] at h
  linarith only [h]

/-- For `s>1`, remove the logarithmic singularity from the Mellin integral and express
it using Euler's constant, the lower endpoint and a finite log-log integral.
Combine integration by parts with the existing Euler-constant moment formula. -/
theorem logMellin_normalized_eq_euler {s : ℝ} (hs : 1 < s) :
    (∫ t : ℝ in Set.Ioi 2, t ^ (-s) / Real.log t) + Real.log (s - 1) =
      -Real.eulerMascheroniConstant - Real.log (Real.log 2) * (2 : ℝ) ^ (1 - s) -
        (s - 1) * ∫ t : ℝ in (1 : ℝ)..2, Real.log (Real.log t) * t ^ (-s) := by
  have hg := Real.eulerMascheroniConstant_eq_neg_integral_log_log hs
  have hi :=
    intervalIntegral.integral_Ioi_sub_Ioi (Real.integrableOn_log_log_mul_rpow hs)
      (by norm_num only : (1 : ℝ) ≤ 2)
  have ht :
    (∫ t : ℝ in Set.Ioi 2, Real.log (Real.log t) * t ^ (-s)) =
      (∫ t : ℝ in Set.Ioi 1, Real.log (Real.log t) * t ^ (-s)) -
        ∫ t : ℝ in (1 : ℝ)..2, Real.log (Real.log t) * t ^ (-s) := by
    linarith only [hi]
  rw [logMellin_eq_logLog_integral hs, ht]
  nlinarith only [hg]

/-- The log-log Mellin moment on `[1,2]` converges as the exponent approaches one
from above. Dominate by four times the absolute exponent-two moment, including
the integrable logarithmic singularity at the lower endpoint. -/
theorem tendsto_logLogMellin_low_integral :
    Filter.Tendsto (fun s : ℝ ↦ ∫ t : ℝ in (1 : ℝ)..2, Real.log (Real.log t) * t ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (∫ t : ℝ in (1 : ℝ)..2, Real.log (Real.log t) * t ^ (-(1 : ℝ)))) := by
  have hi :=
    (Real.integrableOn_log_log_mul_rpow (by norm_num only : (1 : ℝ) < 2)).mono_set
      (show Set.Ioc (1 : ℝ) 2 ⊆ Set.Ioi 1 from fun t ht ↦ ht.1)
  have hbound :
    MeasureTheory.Integrable (fun t : ℝ ↦ 4 * |Real.log (Real.log t) * t ^ (-(2 : ℝ))|)
      (MeasureTheory.volume.restrict (Set.Ioc 1 2)) := by
    simpa only [Real.norm_eq_abs] using hi.norm.const_mul 4
  simp only [intervalIntegral.integral_of_le (by norm_num only : (1 : ℝ) ≤ 2)]
  apply
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ ↦ 4 * |Real.log (Real.log t) * t ^ (-(2 : ℝ))|) ?_ ?_ hbound ?_
  · exact
      Filter.Eventually.of_forall
        (fun s ↦
          ((Real.measurable_log.comp Real.measurable_log).mul
              (measurable_id.pow_const (-s))).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    have hp1 : t ^ (-s) ≤ 1 := by
      have h :=
        Real.rpow_le_rpow_of_exponent_le ht.1.le
          (by linarith only [(show 1 < s from hs)] : -s ≤ (0 : ℝ))
      simpa only [Real.rpow_zero] using h
    have hp2 : 1 ≤ 4 * t ^ (-(2 : ℝ)) := by
      have h := Real.rpow_le_rpow_of_nonpos ht0 ht.2 (by norm_num only : (-(2 : ℝ)) ≤ 0)
      norm_num only [Real.rpow_neg (by norm_num only : (0 : ℝ) ≤ 2), Real.rpow_two] at h
      linarith only [h]
    change ‖Real.log (Real.log t) * t ^ (-s)‖ ≤ 4 * |Real.log (Real.log t) * t ^ (-(2 : ℝ))|
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le (-s)),
      abs_of_nonneg (Real.rpow_nonneg ht0.le (-(2 : ℝ)))]
    nlinarith only [mul_le_mul_of_nonneg_left (hp1.trans hp2) (abs_nonneg (Real.log (Real.log t)))]
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hc : ContinuousAt (fun s : ℝ ↦ Real.log (Real.log t) * t ^ (-s)) 1 :=
      continuousAt_const.mul
        ((Real.continuous_const_rpow (zero_lt_one.trans ht.1).ne').continuousAt.comp
          continuousAt_id.neg)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-- As the exponent tends to one from above, the reciprocal-logarithmic Mellin
integral plus `log(s-1)` tends to `-gamma-log(log 2)`.
The finite low-interval correction vanishes after multiplication by `s-1`. -/
theorem tendsto_logMellin_normalized :
    Filter.Tendsto (fun s : ℝ ↦ (∫ t : ℝ in Set.Ioi 2, t ^ (-s) / Real.log t) + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (-Real.eulerMascheroniConstant - Real.log (Real.log 2))) := by
  have hp : Filter.Tendsto (fun s : ℝ ↦ (2 : ℝ) ^ (1 - s)) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    have hc : ContinuousAt (fun s : ℝ ↦ (2 : ℝ) ^ (1 - s)) 1 :=
      (Real.continuous_const_rpow (by norm_num only : (2 : ℝ) ≠ 0)).continuousAt.comp
        (continuousAt_const.sub continuousAt_id)
    have h :
      Filter.Tendsto (fun s : ℝ ↦ (2 : ℝ) ^ (1 - s)) (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((2 : ℝ) ^ ((1 : ℝ) - 1))) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self, Real.rpow_zero] using h
  have hid : Filter.Tendsto (fun s : ℝ ↦ s - 1) (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    have hc : ContinuousAt (fun s : ℝ ↦ s - 1) 1 := continuousAt_id.sub continuousAt_const
    have h : Filter.Tendsto (fun s : ℝ ↦ s - 1) (nhdsWithin 1 (Set.Ioi 1)) (nhds ((1 : ℝ) - 1)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using h
  have hright :
    Filter.Tendsto
      (fun s : ℝ ↦
        -Real.eulerMascheroniConstant - Real.log (Real.log 2) * (2 : ℝ) ^ (1 - s) -
          (s - 1) * ∫ t : ℝ in (1 : ℝ)..2, Real.log (Real.log t) * t ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (-Real.eulerMascheroniConstant - Real.log (Real.log 2))) := by
    simpa only [mul_one, zero_mul, sub_zero] using
      ((tendsto_const_nhds (x := -Real.eulerMascheroniConstant)).sub
            ((tendsto_const_nhds (x := Real.log (Real.log 2))).mul hp)).sub
        (hid.mul tendsto_logLogMellin_low_integral)
  refine Filter.Tendsto.congr' ?_ hright
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (logMellin_normalized_eq_euler hs).symm

end PseudoPrime.Analysis
