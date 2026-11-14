/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundTheta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundCountTheta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaRemainder
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaComplexIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaCellPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Two-sided zero-count error and normalized argument -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The closed-endpoint positive zero count minus the smooth Gamma phase
and one. At good heights this is the Euler-normalized zeta argument divided
by π; at zero heights its value follows the closed counting convention. -/
@[expose]
noncomputable def zetaArgCount (t : ℝ) : ℝ :=
  positiveZeroCount t - 1 - backlundTheta t / Real.pi

/-- The two-sided zero count minus the Riemann–von Mangoldt main term.
This closed-endpoint discrepancy is the error integrated in zero-tail bounds. -/
@[expose]
noncomputable def zeroCountError (t : ℝ) : ℝ :=
  zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)

/-- Under RH, the two-sided count error is twice the normalized argument
plus twice the normalized Gamma phase error. This identity holds at every
positive height, including zeros, using the closed-endpoint count. -/
theorem zeroCountError_eq_arg (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t) :
    zeroCountError t = 2 * zetaArgCount t + 2 * backlundThetaError t := by
  have hlog := Real.log_div ht.ne' (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).ne'
  have hcount := zeroCount_eq_two_positive hRH ht.le
  have hpi : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  simp only [zeroCountError, zetaArgCount, backlundThetaError, backlundThetaMain]
  rw [hcount, hlog]
  simp only [div_eq_mul_inv]
  nlinarith only [hpi]

/-- At heights at least 100, twice the normalized Gamma phase error has
absolute value at most `2 / (5 * t)`. The existing Euler–Maclaurin
remainder supplies the bound without a zero table or RH. -/
theorem thetaError_twice_le {t : ℝ} (ht : 100 ≤ t) : |2 * backlundThetaError t| ≤ 2 / (5 * t) := by
  have ht0 : 0 < t := by linarith only [ht]
  have hbase : 2 * Real.pi * Real.exp 1 ≤ t := by
    have hm :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hm, ht]
  have hR :=
    gamma_remainder_bounds_of_integral
      (gamma_remainder_identity_of_complex backlund_gamma_complex_identity) t hbase
  have hG := backlundTheta_error_of_signed_remainder ht0 hR.1 hR.2
  have h := theta_error_le_of_phase ht0 hG
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  convert mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num only) using 1
  ring

/-- The normalized Gamma phase is continuous at every real height. Its
Euler logarithm is holomorphic at the argument with real part one quarter. -/
theorem continuousAt_backlundTheta (t : ℝ) : ContinuousAt backlundTheta t := by
  let z : ℂ := (((1 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)
  have hz : 0 < z.re := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  have hf := (Gamma.hasDerivAt_logGammaSeries hz).continuousAt
  have ha : ContinuousAt (fun v : ℝ ↦ (((1 / 4 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I)) t :=
    ((continuous_const.add
        ((Complex.continuous_ofReal.comp (continuous_id.div_const 2)).mul
          continuous_const))).continuousAt
  have hc :
    ContinuousAt
      (fun v : ℝ ↦ (Gamma.logGammaSeries (((1 / 4 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I)).im)
      t := by
    have hcomp :
      ContinuousAt
        (fun v : ℝ ↦ Gamma.logGammaSeries (((1 / 4 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I)) t :=
      ContinuousAt.comp (f := fun v : ℝ ↦ (((1 / 4 : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * Complex.I)) hf ha
    exact Complex.continuous_im.continuousAt.comp hcomp
  have hd : ContinuousAt (fun v : ℝ ↦ (v / 2) * Real.log Real.pi) t :=
    ((continuous_id.div_const 2).mul continuous_const).continuousAt
  exact hc.sub hd

/-- The normalized Gamma phase error is continuous at every positive
height. The logarithm in its elementary main term has positive argument. -/
theorem continuousAt_backlundThetaError {t : ℝ} (ht : 0 < t) :
    ContinuousAt backlundThetaError t := by
  have harg : (t / (2 * Real.pi)) ≠ 0 :=
    div_ne_zero ht.ne' (mul_ne_zero (by norm_num only) Real.pi_ne_zero)
  have hlog : ContinuousAt (fun v : ℝ ↦ Real.log (v / (2 * Real.pi))) t :=
    ContinuousAt.comp (f := fun v : ℝ ↦ v / (2 * Real.pi)) (Real.continuousAt_log harg)
      (continuous_id.div_const (2 * Real.pi)).continuousAt
  have hm : ContinuousAt backlundThetaMain t := by
    exact
      ((((continuous_id.div_const 2).continuousAt.mul hlog).sub
            (continuous_id.div_const 2).continuousAt).sub
        continuousAt_const)
  exact ((continuousAt_backlundTheta t).sub hm).div_const Real.pi

/-- Between ordered heights at least 100, the integral of twice the
normalized Gamma error has absolute value at most `(2/5) log(v/u)`.
Integrate the pointwise reciprocal bound on the positive interval. -/
theorem thetaError_integral_le {u v : ℝ} (hu : 100 ≤ u) (huv : u ≤ v) :
    |∫ t in u..v, 2 * backlundThetaError t| ≤ (2 / 5 : ℝ) * Real.log (v / u) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hInt :
    IntervalIntegrable (fun t : ℝ ↦ 2 * backlundThetaError t) MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    intro t ht
    exact
      (continuousAt_const.mul
          (continuousAt_backlundThetaError (hu0.trans_le ht.1))).continuousWithinAt
  have hInt' : IntervalIntegrable (fun t : ℝ ↦ (2 / 5 : ℝ) * (1 / t)) MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    apply ContinuousOn.const_mul
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    exact (hu0.trans_le ht.1).ne'
  have hm :=
    intervalIntegral.integral_mono_on huv hInt.norm hInt'
      (fun t ht ↦ by
        have hh := thetaError_twice_le (le_trans hu ht.1)
        rw [Real.norm_eq_abs]
        convert hh using 1
        ring)
  have hnorm :=
    intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := fun t : ℝ ↦
      2 * backlundThetaError t) huv
  rw [Real.norm_eq_abs] at hnorm
  have h0 : (0 : ℝ) ∉ Set.uIcc u v := by
    rw [Set.uIcc_of_le huv]
    intro h
    linarith only [h.1, hu0]
  rw [intervalIntegral.integral_const_mul, integral_one_div h0] at hm
  exact hnorm.trans hm

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
