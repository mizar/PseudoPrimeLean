/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountArgumentRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalLogZetaRH

/-! # Integrating the zero-count and Gamma-phase errors -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the normalized count-defined argument is interval integrable
on positive ordered intervals. The positive zero count is half the integrable
two-sided count, and the Gamma phase is continuous. -/
theorem zetaArgCount_integrable (hRH : RiemannHypothesis) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    IntervalIntegrable zetaArgCount MeasureTheory.volume u v := by
  have hp : IntervalIntegrable positiveZeroCount MeasureTheory.volume u v := by
    have h := (zeroCount_integrable hu.le huv).div_const (2 : ℝ)
    apply h.congr
    intro t ht
    rw [Set.uIoc_of_le huv] at ht
    change zeroCount t / 2 = positiveZeroCount t
    rw [zeroCount_eq_two_positive hRH (hu.le.trans ht.1.le)]
    ring
  have ht : IntervalIntegrable (fun t ↦ backlundTheta t / Real.pi) MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    intro t ht
    exact ((continuousAt_backlundTheta t).div_const Real.pi).continuousWithinAt
  exact (hp.sub intervalIntegrable_const).sub ht

/-- Under RH, the proposed coarse integral bound for the count-defined
argument implies the corresponding two-sided zero-count error bound.
The remaining Gamma phase error is integrated explicitly and separately. -/
theorem countError_integral_of_arg (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u) (huv : u ≤ v)
    (harg : |∫ t in u..v, zetaArgCount t| ≤ 8 + (7 / 10 : ℝ) * Real.log v) :
    |∫ t in u..v, zeroCountError t| ≤
      16 + (7 / 5 : ℝ) * Real.log v + (2 / 5 : ℝ) * Real.log (v / u) := by
  have hu0 : 0 < u := by linarith only [hu]
  have hIntArg := zetaArgCount_integrable hRH hu0 huv
  have htheta :
    IntervalIntegrable (fun t : ℝ ↦ 2 * backlundThetaError t) MeasureTheory.volume u v := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le huv]
    intro t ht
    exact
      (continuousAt_const.mul
          (continuousAt_backlundThetaError (hu0.trans_le ht.1))).continuousWithinAt
  have heq :
    (∫ t in u..v, zeroCountError t) =
      (∫ t in u..v, 2 * zetaArgCount t) + (∫ t in u..v, 2 * backlundThetaError t) := by
    rw [← intervalIntegral.integral_add (hIntArg.const_mul 2) htheta]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    exact zeroCountError_eq_arg hRH (hu0.trans_le ht.1)
  rw [heq, intervalIntegral.integral_const_mul]
  have ha := abs_add_le (2 * ∫ t in u..v, zetaArgCount t) (∫ t in u..v, 2 * backlundThetaError t)
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)] at ha
  have ht := thetaError_integral_le hu huv
  nlinarith only [ha, harg, ht]

/-- Under RH, the horizontal-logarithm identity for the count-defined
argument yields the explicit integrated zero-count error estimate at
ordered heights at least 100. The horizontal bounds and gamma error are
supplied internally; the identity remains the analytic input. -/
theorem countError_integral_of_horizontal (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u)
    (huv : u ≤ v)
    (hidentity :
      Real.pi * (∫ t in u..v, zetaArgCount t) =
        (∫ x in Set.Ioi (0 : ℝ),
            Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖) -
          (∫ x in Set.Ioi (0 : ℝ),
            Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖)) :
    |∫ t in u..v, zeroCountError t| ≤
      16 + (7 / 5 : ℝ) * Real.log v + (2 / 5 : ℝ) * Real.log (v / u) := by
  apply countError_integral_of_arg hRH hu huv
  have hh := RiemannXi.abs_horizontal_logZeta_diff_le hRH hu huv
  rw [← hidentity, abs_mul, abs_of_pos Real.pi_pos] at hh
  have hl : 0 ≤ Real.log v := Real.log_nonneg (by linarith only [hu, huv])
  have hp := Real.pi_gt_three
  have hm := mul_nonneg (sub_nonneg.mpr hp.le) (abs_nonneg (∫ t in u..v, zetaArgCount t))
  nlinarith only [hh, hl, hm]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
