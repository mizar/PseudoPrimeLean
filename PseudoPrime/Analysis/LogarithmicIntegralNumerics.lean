/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogDirichletNumericalBounds
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import PseudoPrime.Analysis.LogarithmicDecay

/-! # A numerical bound for the common logarithmic inverse-square integral

A two-region positive-half-line envelope has integral eleven.
Its reflection controls the whole real line with bound twenty-two.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The positive-half-line envelope is five on [0,1] and
(log(t)+5)*t^(-2) on (1,infinity), written as two integrable tail terms.
It is zero on negative inputs. Its exact integral controls the common
logarithmic inverse-square integral used in triangular remainder bounds. -/
noncomputable def logarithmicIntegralPositiveProfile (t : ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) 1).indicator (fun _ ↦ (5 : ℝ)) t +
    (Set.Ioi (1 : ℝ)).indicator (fun u ↦ (Real.log u + 1) * u ^ (-2 : ℝ) + 4 * u ^ (-2 : ℝ)) t

/-- The positive-half-line envelope is integrable. Combine a bounded
constant region, the proved logarithmic-power envelope, and an inverse-square
tail. This justifies the explicit whole-line envelope integral. -/
theorem logarithmicIntegralPositiveProfile_integrable :
    MeasureTheory.Integrable logarithmicIntegralPositiveProfile := by
  have hc :=
    (continuous_const : Continuous (fun _ : ℝ ↦ (5 : ℝ))).continuousOn |>.integrableOn_Icc (μ :=
      MeasureTheory.volume) (a := 0) (b := 1)
  have he := integrableOn_logPower_envelope (by norm_num only : (0 : ℝ) < 1)
  norm_num only at he
  have hp :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-2 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      4
  exact
    (hc.integrable_indicator measurableSet_Icc).add
      ((he.add hp).integrable_indicator measurableSet_Ioi)

/-- The positive-half-line envelope has integral eleven: five from [0,1]
and six from the logarithmic inverse-square tail. Integrate both indicator
regions and use the exact logarithmic-power integral at exponent minus two.
This supplies the numerical mass for the symmetric majorant. -/
theorem logarithmicIntegralPositiveProfile_integral :
    (∫ t : ℝ, logarithmicIntegralPositiveProfile t) = 11 := by
  have hc :=
    (continuous_const : Continuous (fun _ : ℝ ↦ (5 : ℝ))).continuousOn |>.integrableOn_Icc (μ :=
      MeasureTheory.volume) (a := 0) (b := 1)
  have he := integrableOn_logPower_envelope (by norm_num only : (0 : ℝ) < 1)
  norm_num only at he
  have hp :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-2 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 1)).const_mul
      4
  have hval := integral_logPower_envelope (by norm_num only : (0 : ℝ) < 1)
  norm_num only at hval
  unfold logarithmicIntegralPositiveProfile
  erw [MeasureTheory.integral_add (hc.integrable_indicator measurableSet_Icc)
      ((he.add hp).integrable_indicator measurableSet_Ioi),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_add he hp, hval,
    MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num only) (by norm_num only),
    MeasureTheory.integral_Icc_eq_integral_Ioc, ←
    intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_const]
  norm_num only [Real.one_rpow, smul_eq_mul]

/-- The positive-half-line envelope is nonnegative at every real input.
The tail is supported where log(t) is nonnegative; indicator values elsewhere
are zero. This permits adding its reflection in the comparison. -/
theorem logarithmicIntegralPositiveProfile_nonneg (t : ℝ) :
    0 ≤ logarithmicIntegralPositiveProfile t := by
  unfold logarithmicIntegralPositiveProfile
  apply add_nonneg (Set.indicator_nonneg (fun _ _ ↦ by norm_num only) t)
  apply Set.indicator_nonneg _ t
  intro u hu
  exact
    add_nonneg
      (mul_nonneg (add_nonneg (Real.log_nonneg hu.le) zero_le_one)
        (Real.rpow_nonneg (zero_le_one.trans hu.le) _))
      (mul_nonneg (by norm_num only) (Real.rpow_nonneg (zero_le_one.trans hu.le) _))

/-- For nonnegative t, the logarithmic inverse-square weight is bounded
by the positive-half-line envelope. On [0,1], use log(5)<=4; on the tail,
use 4+t<=5*t and enlarge the denominator from t^2 to 1+t^2.
This pointwise estimate supplies the whole-line integral comparison. -/
theorem logarithmicIntegralPositiveProfile_upper {t : ℝ} (ht : 0 ≤ t) :
    (Real.log (4 + t) + 1) / (1 + t ^ 2) ≤ logarithmicIntegralPositiveProfile t := by
  have hd : 0 < 1 + t ^ 2 := by linarith only [sq_nonneg t]
  have hlog5 : Real.log 5 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 5)
    norm_num only at h
    exact h
  by_cases ht1 : t ≤ 1
  · have hc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht, ht1⟩
    have htail : t ∉ Set.Ioi (1 : ℝ) := not_lt.mpr ht1
    rw [logarithmicIntegralPositiveProfile, Set.indicator_of_mem hc, Set.indicator_of_notMem htail,
      add_zero]
    have hl : Real.log (4 + t) ≤ Real.log 5 :=
      Real.log_le_log (by linarith only [ht]) (by linarith only [ht1])
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hl, hlog5, sq_nonneg t]
  · have ht1' : 1 < t := lt_of_not_ge ht1
    have htpos : 0 < t := zero_lt_one.trans ht1'
    have hc : t ∉ Set.Icc (0 : ℝ) 1 := fun h ↦ ht1 h.2
    have htail : t ∈ Set.Ioi (1 : ℝ) := ht1'
    rw [logarithmicIntegralPositiveProfile, Set.indicator_of_notMem hc, Set.indicator_of_mem htail,
      zero_add, Real.rpow_neg htpos.le, Real.rpow_two]
    have hl : Real.log (4 + t) ≤ Real.log 5 + Real.log t := by
      have hm :=
        Real.log_le_log (by linarith only [htpos] : 0 < 4 + t)
          (by linarith only [ht1'] : 4 + t ≤ 5 * t)
      rw [Real.log_mul (by norm_num only : (5 : ℝ) ≠ 0) htpos.ne'] at hm
      exact hm
    have hnum : Real.log (4 + t) + 1 ≤ Real.log t + 5 := by linarith only [hl, hlog5]
    have hnp : 0 ≤ Real.log t + 5 := by linarith only [Real.log_nonneg ht1'.le]
    calc
      _ ≤ (Real.log t + 5) / (1 + t ^ 2) := div_le_div_of_nonneg_right hnum hd.le
      _ ≤ (Real.log t + 5) / t ^ 2 :=
        div_le_div_of_nonneg_left hnp (sq_pos_of_pos htpos) (by linarith only [sq_nonneg t])
      _ = _ := by
        rw [div_eq_mul_inv]; ring

/-- The common logarithmic inverse-square integral over the real line
is at most twenty-two. Bound each half-line by the positive envelope and
its reflection, whose integrals are both eleven. This removes the remaining
common-integral input from the triangular reflected and gamma bounds. -/
theorem logarithmic_inverseSquare_integral_le_twenty_two :
    (∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) ≤ 22 := by
  have hi :=
    logarithmicIntegralPositiveProfile_integrable.add
      logarithmicIntegralPositiveProfile_integrable.comp_neg
  have hb (t : ℝ) :
    (Real.log (4 + |t|) + 1) / (1 + t ^ 2) ≤
      logarithmicIntegralPositiveProfile t + logarithmicIntegralPositiveProfile (-t) := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
      exact
        (logarithmicIntegralPositiveProfile_upper ht).trans
          (le_add_of_nonneg_right (logarithmicIntegralPositiveProfile_nonneg (-t)))
    · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
      have h := logarithmicIntegralPositiveProfile_upper ht'
      rw [neg_sq] at h
      rw [abs_of_nonpos (le_of_not_ge ht)]
      exact h.trans (le_add_of_nonneg_left (logarithmicIntegralPositiveProfile_nonneg t))
  have h := MeasureTheory.integral_mono integrable_log_add_abs_div_one_add_sq hi hb
  erw [MeasureTheory.integral_add logarithmicIntegralPositiveProfile_integrable
      logarithmicIntegralPositiveProfile_integrable.comp_neg,
    MeasureTheory.integral_neg_eq_self, logarithmicIntegralPositiveProfile_integral] at h
  norm_num only at h
  exact h

end PseudoPrime.Analysis
