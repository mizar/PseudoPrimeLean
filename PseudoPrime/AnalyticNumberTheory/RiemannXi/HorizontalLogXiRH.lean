/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalPoissonRH
import PseudoPrime.Analysis.ComplexLogPrimitive
import PseudoPrime.Analysis.WeightedDerivativeIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Log

/-! # Horizontal logarithmic derivatives of xi -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The logarithmic norm of xi along any horizontal line is interval
integrable, including at zero ordinates. Its real-analytic restriction is
meromorphic, so the logarithmic singularities are integrable. -/
theorem intervalIntegrable_horizontal_logXi (t a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ ↦ Real.log ‖riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      MeasureTheory.volume a b := by
  have h :
    AnalyticOnNhd ℝ (fun u : ℝ ↦ riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      (Set.uIcc a b) := by
    intro u hu
    have hlin : AnalyticAt ℝ (fun u : ℝ ↦ (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u := by
      have h :=
        (analyticAt_const (v := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).add
          (Complex.ofRealCLM.analyticAt u)
      convert h using 1
      funext v
      simp only [Complex.ofRealCLM_apply, Complex.ofReal_add, Pi.add_apply]
      ring
    exact (differentiable_riemannXi.analyticAt _).restrictScalars.comp hlin
  exact h.meromorphicOn.intervalIntegrable_log_norm

/-- Under RH and at a positive horizontal offset, the derivative of the
logarithmic norm of xi is the real part of its logarithmic derivative.
A local zero-free logarithmic primitive avoids any branch choice. -/
theorem hasDerivAt_horizontal_logXi (hRH : RiemannHypothesis) {u : ℝ} (t : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v : ℝ ↦ Real.log ‖riemannXi (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      (logDeriv riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re u := by
  let c : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let s : ℂ := c + (u : ℂ)
  have hsre : 1 / 2 < s.re := by
    simp only [s, c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu]
  have hs0 : riemannXi s ≠ 0 := fun h ↦ hsre.ne' (xi_zero_re_eq_half_of_riemannHypothesis hRH h)
  have hevent := differentiable_riemannXi.continuous.continuousAt.eventually_ne hs0
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have han : AnalyticOnNhd ℂ riemannXi (Metric.ball s r) := fun z hz ↦
    differentiable_riemannXi.analyticAt z
  obtain ⟨f, hf, hfre⟩ := Analysis.exists_hasDerivAt_logDeriv_re_eq_log_norm hr han hball
  have hsball : s ∈ Metric.ball s r := Metric.mem_ball_self hr
  have ha : HasDerivAt (fun z : ℂ ↦ c + z) 1 (u : ℂ) := by
    simpa only [id_eq] using (hasDerivAt_id (u : ℂ)).const_add c
  have hcomp := (hf s hsball).comp (u : ℂ) ha
  have hreal := hcomp.real_of_complex
  have hnear : ∀ᶠ v : ℝ in nhds u, c + (v : ℂ) ∈ Metric.ball s r := by
    have hc : ContinuousAt (fun v : ℝ ↦ c + (v : ℂ)) u :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    exact hc.eventually (Metric.isOpen_ball.mem_nhds hsball)
  have hEq :
    (fun v : ℝ ↦ Real.log ‖riemannXi (c + (v : ℂ))‖) =ᶠ[nhds u]
      (fun v : ℝ ↦ (f (c + (v : ℂ))).re) := by
    filter_upwards [hnear] with v hv
    exact (hfre _ hv).symm
  have hfreal := hreal.congr_of_eventuallyEq hEq
  simpa only [s, c, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, mul_one, add_assoc, add_comm, add_left_comm] using hfreal

/-- Under RH, the real part of the xi logarithmic derivative varies
continuously along a horizontal line at every positive offset. Analyticity
and nonvanishing give a continuous quotient locally. -/
theorem continuousAt_horizontal_logDeriv (hRH : RiemannHypothesis) {u : ℝ} (t : ℝ) (hu : 0 < u) :
    ContinuousAt (fun v : ℝ ↦ (logDeriv riemannXi (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
      u := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hsre : 1 / 2 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu]
  have hs0 : riemannXi s ≠ 0 := fun h ↦ hsre.ne' (xi_zero_re_eq_half_of_riemannHypothesis hRH h)
  have han := differentiable_riemannXi.analyticAt s
  have he : logDeriv riemannXi = (fun z ↦ deriv riemannXi z / riemannXi z) := by
    funext z
    exact logDeriv_apply _ _
  have hc : ContinuousAt (logDeriv riemannXi) s := by
    rw [he]
    exact (han.deriv.div han hs0).continuousAt
  have ha : ContinuousAt (fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u :=
    ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).add
        continuous_const).continuousAt
  have hc' :
    ContinuousAt (fun v : ℝ ↦ logDeriv riemannXi (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u :=
    ContinuousAt.comp (f := fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) hc ha
  exact Complex.continuous_re.continuousAt.comp hc'

/-- Under RH, on any positive ordered offset interval, the horizontal
integral of the logarithmic xi norm is bounded below by its right endpoint
minus the explicit weighted logarithmic-derivative cost. This is the
finite-left-endpoint form used before taking the critical-line limit. -/
theorem horizontal_logXi_integral_lower (hRH : RiemannHypothesis) (t : ℝ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    (b - a) * Real.log ‖riemannXi (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ -
        b * (b - a) * (logDeriv riemannXi (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      ∫ u in a..b, Real.log ‖riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  apply Analysis.integral_lower_of_weighted_deriv ha.le hab
  · intro u hu
    exact hasDerivAt_horizontal_logXi hRH t (ha.trans_le hu.1)
  · intro u hu
    exact (continuousAt_horizontal_logDeriv hRH t (ha.trans_le hu.1)).continuousWithinAt
  · intro u hu
    apply logDeriv_re_nonneg hRH
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [ha, hu.1]
  · intro u hu
    exact mul_logDeriv_re_mono hRH t (ha.trans_le hu.1) hu.2

/-- Under RH, the integral of the horizontal logarithmic xi norm from the
critical line has the endpoint lower bound used in the integrated zero-count
method. The integral remains valid when its left endpoint is a zero of xi. -/
theorem horizontal_logXi_lower_from_line (hRH : RiemannHypothesis) (t : ℝ) {b : ℝ} (hb : 0 < b) :
    b * Real.log ‖riemannXi (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ -
        b ^ 2 * (logDeriv riemannXi (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re ≤
      ∫ u in (0 : ℝ)..b, Real.log ‖riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  apply Analysis.integral_lower_of_positive_endpoints hb (intervalIntegrable_horizontal_logXi t 0 b)
  intro a ha hab
  exact horizontal_logXi_integral_lower hRH t ha hab

end PseudoPrime.AnalyticNumberTheory.RiemannXi
