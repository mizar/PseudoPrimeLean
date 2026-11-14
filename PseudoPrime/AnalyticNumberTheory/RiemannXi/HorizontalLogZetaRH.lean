/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalLogXiRH
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogFactor
import PseudoPrime.AnalyticNumberTheory.Gamma.TrigammaSpecialValues
import PseudoPrime.AnalyticNumberTheory.Gamma.NumericalDigammaBounds
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonEulerBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripReciprocal
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.EulerLog
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaTailDecay
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaHalfStripCircle
import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogDerivZeta
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroFiniteness

/-! # Horizontal logarithmic norms of zeta and xi -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The horizontal derivative of the non-zeta completion factor at height
`t` and offset `u`. It separates the pole, pi, and shifted digamma terms
needed for the explicit integrated zero-count estimate. -/
noncomputable def horizontalCompletionDeriv (t u : ℝ) : ℝ :=
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  (1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2).re

/-- In the positive half-plane and away from the logarithm's branch cut,
the derivative of the xi completion logarithm is the pole term plus the
shifted digamma term. The digamma recurrence cancels the derivative of
the unshifted factor at zero. -/
theorem hasDerivAt_xiLogFactor {s : ℂ} (hs : 0 < s.re) (hc : s - 1 ∈ Complex.slitPlane) :
    HasDerivAt xiLogFactor
      (1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2) s := by
  have h0 : s ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hs)
  have hp : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    exact div_pos hs (by norm_num only)
  have hg := Gamma.hasDerivAt_logGammaSeries hp
  rw [← Gamma.digamma_eq_resolventSeries hp] at hg
  have hd :=
    (((Complex.hasDerivAt_log h0).comp s (hasDerivAt_id s)).add
          ((Complex.hasDerivAt_log hc).comp s ((hasDerivAt_id s).sub_const 1))).sub
      (((hasDerivAt_id s).div_const 2).mul_const (Real.log Real.pi : ℂ))
  have hh := hd.add (hg.comp s ((hasDerivAt_id s).div_const 2))
  have hrec := Complex.digamma_apply_add_one (s / 2) (Gamma.not_neg_nat_of_re_pos hp)
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  convert hh using 1
  · rfl
  · rw [hrec]
    field_simp
    ring

/-- At a nonzero zeta value in the right half-plane, the logarithmic norm of
xi separates into the zeta logarithmic norm and the real completion factor.
The exponential factorization fixes the normalizing constant. -/
theorem log_norm_xi_eq_factor_add {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    Real.log ‖riemannXi s‖ = (xiLogFactor s).re - Real.log 2 + Real.log ‖riemannZeta s‖ := by
  rw [riemannXi_eq_exp_factor hs hs1, norm_mul, norm_mul,
    Real.log_mul
      (mul_ne_zero (norm_ne_zero_iff.mpr (by norm_num only))
        (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)))
      (norm_ne_zero_iff.mpr hz),
    Real.log_mul (norm_ne_zero_iff.mpr (by norm_num only : (1 / 2 : ℂ) ≠ 0))
      (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)),
    Complex.norm_exp, Real.log_exp]
  have h : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  rw [h, Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0),
    Real.log_one]
  ring

/-- At nonzero height, the real part of the xi completion factor is continuous
from the critical line to any nonnegative horizontal offset. Its logarithm
branches remain regular because the imaginary part is nonzero. -/
theorem continuousOn_horizontal_logFactor (t : ℝ) (ht : t ≠ 0) {b : ℝ} :
    ContinuousOn (fun u : ℝ ↦ (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
      (Set.Icc 0 b) := by
  intro u hu
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hs : 0 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu.1]
  have hc : s - 1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [s, Complex.sub_im, Complex.one_im, sub_zero, Complex.add_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add] using ht
  have hlin : ContinuousAt (fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u :=
    ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).add
        continuous_const).continuousAt
  have hf :
    ContinuousAt (fun v : ℝ ↦ xiLogFactor (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u :=
    ContinuousAt.comp (f := fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      (differentiableAt_xiLogFactor hs hc).continuousAt hlin
  exact (Complex.continuous_re.continuousAt.comp hf).continuousWithinAt

/-- At nonzero height and a nonnegative offset, the real completion factor
has the horizontal derivative given by the pole and shifted digamma terms.
This prepares its weighted integral for the explicit lower bound. -/
theorem hasDerivAt_horizontal_logFactor {t u : ℝ} (ht : t ≠ 0) (hu : 0 ≤ u) :
    HasDerivAt
      (fun v : ℝ ↦ (xiLogFactor (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2)
      ((1 / ((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1) - (Real.log Real.pi : ℂ) / 2 +
          Complex.digamma (((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1) / 2).re)
      u := by
  let c : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let s : ℂ := c + (u : ℂ)
  have hs : 0 < s.re := by
    simp only [s, c, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu]
  have hc : s - 1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa only [s, c, Complex.sub_im, Complex.one_im, sub_zero, Complex.add_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add] using ht
  have ha : HasDerivAt (fun z : ℂ ↦ c + z) 1 (u : ℂ) := by
    simpa only [id_eq] using (hasDerivAt_id (u : ℂ)).const_add c
  have hh := ((hasDerivAt_xiLogFactor hs hc).comp (u : ℂ) ha).real_of_complex
  simpa only [s, c, Function.comp_apply, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, mul_one, add_assoc, add_comm, add_left_comm] using
    hh.sub_const (Real.log 2)

/-- At nonzero height, the completion derivative is continuous on a compact
horizontal interval with nonnegative offset. The shifted gamma argument
stays in the positive half-plane and the pole stays off the path. -/
theorem continuousOn_horizontalCompletionDeriv {t b : ℝ} (ht : t ≠ 0) :
    ContinuousOn (horizontalCompletionDeriv t) (Set.Icc 0 b) := by
  intro u hu
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hs : s - 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [s, Complex.sub_im, Complex.one_im, Complex.zero_im, sub_zero, Complex.add_im,
      Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, zero_add, add_zero] at hi
    exact ht hi
  have hp : 0 < (s / 2 + 1).re := by
    simp only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    linarith only [hu.1]
  have hlin : ContinuousAt (fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u :=
    ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).add
        continuous_const).continuousAt
  have hg : ContinuousAt Complex.digamma (s / 2 + 1) :=
    (Gamma.analyticAt_digamma (analyticAt_Gamma_of_re_pos hp)
        (Complex.Gamma_ne_zero_of_re_pos hp)).continuousAt
  have hh :
    ContinuousAt
      (fun v : ℝ ↦
        1 / (((((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - 1) - (Real.log Real.pi : ℂ) / 2 +
          Complex.digamma (((((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1) / 2)
      u := by
    exact
      ((continuousAt_const.div (hlin.sub_const 1) hs).sub continuousAt_const).add
        ((ContinuousAt.comp (f := fun v : ℝ ↦
              (((((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1)) hg
              ((hlin.div_const 2).add_const 1)).div_const
          2)
  exact (Complex.continuous_re.continuousAt.comp hh).continuousWithinAt

/-- At every nonnegative horizontal offset, the completion derivative differs
from the logarithm of the shifted gamma argument by at most four plus the
absolute real pole term. The uniform digamma error supplies the constant. -/
theorem horizontal_completion_deriv_error (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    |horizontalCompletionDeriv t u - (Real.log ‖s / 2 + 1‖ - Real.log Real.pi) / 2| ≤
      |(1 / (s - 1)).re| + 4 := by
  dsimp only
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hs : (1 / 2 : ℝ) ≤ (s / 2 + 1).re := by
    simp only [s, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero]
    linarith only [hu]
  have hd := (Gamma.abs_re_digamma_sub_log_norm_le hs).trans Gamma.digammaLogErrorBound_le_eight
  have ha :=
    abs_add_le ((1 / (s - 1)).re) (((Complex.digamma (s / 2 + 1)).re - Real.log ‖s / 2 + 1‖) / 2)
  rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num only)] at ha
  have he :
    horizontalCompletionDeriv t u - (Real.log ‖s / 2 + 1‖ - Real.log Real.pi) / 2 =
      (1 / (s - 1)).re + ((Complex.digamma (s / 2 + 1)).re - Real.log ‖s / 2 + 1‖) / 2 := by
    simp only [horizontalCompletionDeriv, s, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.div_ofNat_re]
    ring
  rw [he]
  linarith only [ha, hd]

/-- At nonzero height the real part of the pole term is bounded by the
reciprocal height. The imaginary part provides a lower bound for the norm
of the denominator independently of the horizontal offset. -/
theorem horizontal_pole_le (u : ℝ) {t : ℝ} (ht : t ≠ 0) :
    |(1 / (((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - 1)).re| ≤ |t|⁻¹ := by
  let z : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1
  have hn : |t| ≤ ‖z‖ := by
    have h := Complex.abs_im_le_norm z
    simpa only [z, Complex.sub_im, Complex.one_im, sub_zero, Complex.add_im, Complex.ofReal_im,
      Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add,
      add_zero] using h
  have hp : 0 < |t| := abs_pos.mpr ht
  have hi := one_div_le_one_div_of_le hp hn
  rw [one_div, one_div] at hi
  have hr := Complex.abs_re_le_norm (z⁻¹)
  rw [norm_inv] at hr
  change |(1 / z).re| ≤ |t|⁻¹
  rw [one_div]
  exact hr.trans hi

/-- Pointwise bounds for the pole term and the shifted logarithm give a
uniform bound for the completion derivative. The digamma contribution is
supplied by the explicit constant four. -/
theorem horizontal_completion_uniform {t b k P Q : ℝ}
    (hP : ∀ u ∈ Set.Icc 0 b, |(1 / (((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - 1)).re| ≤ P)
    (hQ :
      ∀ u ∈ Set.Icc 0 b,
        |(Real.log ‖(((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1)‖ - Real.log Real.pi) /
                2 -
              k| ≤
          Q) :
    ∀ u ∈ Set.Icc 0 b, |horizontalCompletionDeriv t u - k| ≤ 4 + P + Q := by
  intro u hu
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  let v : ℝ := (Real.log ‖s / 2 + 1‖ - Real.log Real.pi) / 2
  have hd := horizontal_completion_deriv_error t hu.1
  have ha := abs_sub_le (horizontalCompletionDeriv t u) v k
  have hp := hP u hu
  have hq := hQ u hu
  dsimp only [s, v] at ha
  linarith only [hd, ha, hp, hq]

/-- At nonzero height, integration by parts expresses the integral of the
completion factor using its right endpoint and the weighted pole-digamma
derivative. The identity includes the critical-line endpoint. -/
theorem integral_horizontal_completion {t b : ℝ} (ht : t ≠ 0) (hb : 0 ≤ b) :
    (∫ u in (0 : ℝ)..b, u * horizontalCompletionDeriv t u) =
      b * ((xiLogFactor (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2) -
        ∫ u in (0 : ℝ)..b,
          (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2 := by
  have hf :
    ContinuousOn
      (fun u : ℝ ↦ (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2)
      (Set.uIcc 0 b) := by
    rw [Set.uIcc_of_le hb]
    exact (continuousOn_horizontal_logFactor t ht).sub continuousOn_const
  have hd : IntervalIntegrable (horizontalCompletionDeriv t) MeasureTheory.volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb]
    exact continuousOn_horizontalCompletionDeriv ht
  have h :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (u := fun x : ℝ ↦ x) (v :=
      fun u : ℝ ↦ (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2)
      (u' := fun _ : ℝ ↦ 1) (v' := horizontalCompletionDeriv t) continuous_id.continuousOn hf
      (fun x hx ↦ hasDerivAt_id x)
      (fun x hx ↦ by
        rw [min_eq_left hb, max_eq_right hb] at hx
        exact hasDerivAt_horizontal_logFactor ht hx.1.le)
      intervalIntegrable_const hd
  simpa only [zero_mul, sub_zero, one_mul] using h

/-- Under RH, at nonzero height and positive horizontal offset, the zeta
logarithmic norm is the xi logarithmic norm minus the completion factor.
Nonvanishing follows from the zero-free half-plane implied by RH. -/
theorem horizontal_logZeta_eq (hRH : RiemannHypothesis) {t u : ℝ} (ht : t ≠ 0) (hu : 0 < u) :
    Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ =
      Real.log ‖riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ -
        ((xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2) := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hs : 1 / 2 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu]
  have hs1 : s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_im, Complex.I_re, Complex.one_im, mul_one, mul_zero, zero_add, add_zero] at hi
    exact ht hi
  have hx : riemannXi s ≠ 0 := fun h ↦ hs.ne' (xi_zero_re_eq_half_of_riemannHypothesis hRH h)
  have hz : riemannZeta s ≠ 0 := by
    intro h
    apply hx
    rw [riemannXi_eq_exp_factor (by linarith only [hs]) hs1, h, mul_zero]
  have he := log_norm_xi_eq_factor_add (by linarith only [hs]) hs1 hz
  change Real.log ‖riemannZeta s‖ = Real.log ‖riemannXi s‖ - ((xiLogFactor s).re - Real.log 2)
  linarith only [he]

/-- Under RH and at nonzero height, the horizontal zeta logarithmic norm is
integrable from the critical line. The possible endpoint zero is harmless:
the xi factorization holds on the left-open interval used by the integral. -/
theorem intervalIntegrable_horizontal_logZeta (hRH : RiemannHypothesis) {t b : ℝ} (ht : t ≠ 0)
    (hb : 0 ≤ b) :
    IntervalIntegrable
      (fun u : ℝ ↦ Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      MeasureTheory.volume 0 b := by
  have hf :
    IntervalIntegrable
      (fun u : ℝ ↦ (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2)
      MeasureTheory.volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb]
    exact (continuousOn_horizontal_logFactor t ht).sub continuousOn_const
  apply ((intervalIntegrable_horizontal_logXi t 0 b).sub hf).congr
  intro u hu
  rw [Set.uIoc_of_le hb] at hu
  exact (horizontal_logZeta_eq hRH ht hu.1).symm

/-- Under RH and at nonzero height, the horizontal zeta logarithmic integral
inherits the xi endpoint lower bound after subtracting the explicit
completion-factor integral. This remains valid at a critical-line zero. -/
theorem horizontal_logZeta_lower (hRH : RiemannHypothesis) {t b : ℝ} (ht : t ≠ 0) (hb : 0 < b) :
    b * Real.log ‖riemannXi (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ -
        b ^ 2 * (logDeriv riemannXi (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re -
        (∫ u in (0 : ℝ)..b,
          (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2) ≤
      ∫ u in (0 : ℝ)..b, Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hf :
    IntervalIntegrable
      (fun u : ℝ ↦ (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2)
      MeasureTheory.volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb.le]
    exact (continuousOn_horizontal_logFactor t ht).sub continuousOn_const
  have he :
    (∫ u in (0 : ℝ)..b, Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) =
      (∫ u in (0 : ℝ)..b, Real.log ‖riemannXi (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) -
        (∫ u in (0 : ℝ)..b,
          (xiLogFactor (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re - Real.log 2) := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_horizontal_logXi t 0 b) hf]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    rw [Set.uIoc_of_le hb.le] at hu
    exact horizontal_logZeta_eq hRH ht hu.1
  rw [he]
  linarith only [horizontal_logXi_lower_from_line hRH t hb]

/-- Under RH and at nonzero height, the lower bound for the horizontal
zeta logarithmic integral separates the zeta endpoint from the weighted
completion derivative. The endpoint need only lie right of the critical line. -/
theorem horizontal_logZeta_lower_separated (hRH : RiemannHypothesis) {t b : ℝ} (ht : t ≠ 0)
    (hb : 0 < b) :
    let s : ℂ := (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    b * Real.log ‖riemannZeta s‖ - b ^ 2 * (logDeriv riemannZeta s).re +
          (∫ u in (0 : ℝ)..b, u * horizontalCompletionDeriv t u) -
        b ^ 2 * horizontalCompletionDeriv t b ≤
      ∫ u in (0 : ℝ)..b, Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  dsimp only
  let s : ℂ := (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hs : 1 / 2 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hb]
  have hs1 : s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_im, Complex.I_re, Complex.one_im, mul_one, mul_zero, zero_add, add_zero] at hi
    exact ht hi
  have hx : riemannXi s ≠ 0 := fun h ↦ hs.ne' (xi_zero_re_eq_half_of_riemannHypothesis hRH h)
  have hz : riemannZeta s ≠ 0 := by
    intro h
    apply hx
    rw [riemannXi_eq_exp_factor (by linarith only [hs]) hs1, h, mul_zero]
  have hd := logDeriv_eq_pole_gamma_zeta_of_regular (s := s) (by linarith only [hs]) hs1 hz
  have hdr :
    (logDeriv riemannXi s).re = horizontalCompletionDeriv t b + (logDeriv riemannZeta s).re := by
    rw [hd, ← Complex.ofReal_log Real.pi_pos.le]
    simp only [horizontalCompletionDeriv, s, Complex.add_re, Complex.sub_re, Complex.ofReal_re,
      Complex.div_ofNat_re]
  have he := horizontal_logZeta_eq hRH ht hb
  have hi := integral_horizontal_completion ht hb.le
  have hl := horizontal_logZeta_lower hRH ht hb
  change Real.log ‖riemannZeta s‖ = Real.log ‖riemannXi s‖ - ((xiLogFactor s).re - Real.log 2) at he
  change
    (logDeriv riemannXi s).re = horizontalCompletionDeriv t b + (logDeriv riemannZeta s).re at hdr
  rw [hdr] at hl
  dsimp only [s] at he hl
  have hem := congrArg (fun y : ℝ ↦ b * y) he
  nlinarith only [hem, hi, hl]

/-- A uniform error bound for the horizontal completion derivative controls
its weighted contribution to the zeta logarithmic integral. The constant
part is integrated exactly and the error is bounded at the endpoint and
under the nonnegative weight. -/
theorem horizontal_completion_cost {t b k E : ℝ} (ht : t ≠ 0) (hb : 0 ≤ b)
    (hE : ∀ u ∈ Set.Icc 0 b, |horizontalCompletionDeriv t u - k| ≤ E) :
    -(b ^ 2 / 2) * k - (3 * b ^ 2 / 2) * E ≤
      (∫ u in (0 : ℝ)..b, u * horizontalCompletionDeriv t u) -
        b ^ 2 * horizontalCompletionDeriv t b := by
  have hg :
    IntervalIntegrable (fun u : ℝ ↦ u * horizontalCompletionDeriv t u) MeasureTheory.volume 0
      b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb]
    exact continuous_id.continuousOn.mul (continuousOn_horizontalCompletionDeriv ht)
  have hf : IntervalIntegrable (fun u : ℝ ↦ u * (k - E)) MeasureTheory.volume 0 b :=
    (continuous_id.mul continuous_const).intervalIntegrable 0 b
  have hI :=
    intervalIntegral.integral_mono_on hb hf hg
      (fun u hu ↦ by
        have hd := (abs_le.mp (hE u hu)).1
        have hm :=
          mul_le_mul_of_nonneg_left
            (show k - E ≤ horizontalCompletionDeriv t u by linarith only [hd]) hu.1
        exact hm)
  have hid : (∫ u in (0 : ℝ)..b, u) = b ^ 2 / 2 := by
    simpa only [pow_one, Nat.cast_one, one_add_one_eq_two, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, sub_zero] using (integral_pow (a := 0) (b := b) 1)
  rw [intervalIntegral.integral_mul_const, hid] at hI
  have hend := (abs_le.mp (hE b ⟨hb, le_rfl⟩)).2
  have hmul :=
    mul_le_mul_of_nonneg_left (show horizontalCompletionDeriv t b ≤ k + E by linarith only [hend])
      (sq_nonneg b)
  nlinarith only [hI, hmul]

/-- Under RH, a uniform completion-derivative error converts the horizontal
zeta integral into an explicit endpoint lower bound. This isolates the
remaining pointwise pole and digamma estimate for the height-100 argument. -/
theorem horizontal_logZeta_lower_of_completion_bound (hRH : RiemannHypothesis) {t b k E : ℝ}
    (ht : t ≠ 0) (hb : 0 < b) (hE : ∀ u ∈ Set.Icc 0 b, |horizontalCompletionDeriv t u - k| ≤ E) :
    let s : ℂ := (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    b * Real.log ‖riemannZeta s‖ - b ^ 2 * (logDeriv riemannZeta s).re - (b ^ 2 / 2) * k -
        (3 * b ^ 2 / 2) * E ≤
      ∫ u in (0 : ℝ)..b, Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have hc := horizontal_completion_cost ht hb.le hE
  have hz := horizontal_logZeta_lower_separated hRH ht hb
  dsimp only at hz ⊢
  linarith only [hc, hz]

/-- Under RH, explicit pole and shifted-logarithm bounds on the horizontal
segment yield an endpoint lower bound for the zeta logarithmic integral.
The remaining completion-factor error is the fixed digamma allowance four. -/
theorem horizontal_logZeta_lower_of_pole_log (hRH : RiemannHypothesis) {t b k P Q : ℝ} (ht : t ≠ 0)
    (hb : 0 < b)
    (hP : ∀ u ∈ Set.Icc 0 b, |(1 / (((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - 1)).re| ≤ P)
    (hQ :
      ∀ u ∈ Set.Icc 0 b,
        |(Real.log ‖(((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1)‖ - Real.log Real.pi) /
                2 -
              k| ≤
          Q) :
    let s : ℂ := (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    b * Real.log ‖riemannZeta s‖ - b ^ 2 * (logDeriv riemannZeta s).re - (b ^ 2 / 2) * k -
        (3 * b ^ 2 / 2) * (4 + P + Q) ≤
      ∫ u in (0 : ℝ)..b, Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  exact horizontal_logZeta_lower_of_completion_bound hRH ht hb (horizontal_completion_uniform hP hQ)

/-- Under RH, the horizontal zeta integral has an explicit endpoint lower
bound once the shifted logarithm is compared with a chosen center. The pole
term is bounded internally by the reciprocal of the nonzero height. -/
theorem horizontal_logZeta_lower_of_log_bound (hRH : RiemannHypothesis) {t b k Q : ℝ} (ht : t ≠ 0)
    (hb : 0 < b)
    (hQ :
      ∀ u ∈ Set.Icc 0 b,
        |(Real.log ‖(((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1)‖ - Real.log Real.pi) /
                2 -
              k| ≤
          Q) :
    let s : ℂ := (((1 / 2 + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    b * Real.log ‖riemannZeta s‖ - b ^ 2 * (logDeriv riemannZeta s).re - (b ^ 2 / 2) * k -
        (3 * b ^ 2 / 2) * (4 + |t|⁻¹ + Q) ≤
      ∫ u in (0 : ℝ)..b, Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  apply horizontal_logZeta_lower_of_pole_log hRH ht hb
  · intro u hu
    exact horizontal_pole_le u ht
  · exact hQ

/-- At height at least 100, the reciprocal-pole allowance and the quadratic
logarithmic allowance fit in the explicit completion error 81/20. This
arithmetic comparison is used after the shifted-logarithm estimate. -/
theorem completion_error_le_81_20 {t : ℝ} (ht : 100 ≤ t) : 4 + t⁻¹ + 4 / t ^ 2 ≤ 81 / 20 := by
  have ht0 : 0 < t := by linarith only [ht]
  have hs : 10000 ≤ t ^ 2 := by nlinarith only [ht]
  have hi : t⁻¹ ≤ 1 / 100 := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 100 by norm_num only) ht
    simpa only [one_div] using h
  have hq : 4 / t ^ 2 ≤ 1 / 2500 := by
    apply (div_le_iff₀ (sq_pos_of_pos ht0)).2
    linarith only [hs]
  linarith only [hi, hq]

/-- If a positive radius lies between a positive height and the radius
whose square is 16 larger, their logarithms differ by at most the stated
inverse-square allowance. The logarithm is bounded after squaring. -/
theorem log_radius_error {r t : ℝ} (ht : 0 < t) (htr : t ≤ r) (hs : r ^ 2 ≤ t ^ 2 + 16) :
    |(Real.log r - Real.log t) / 2| ≤ 4 / t ^ 2 := by
  have hr : 0 < r := ht.trans_le htr
  have hlog : 0 ≤ Real.log r - Real.log t := sub_nonneg.mpr (Real.log_le_log ht htr)
  rw [abs_of_nonneg (div_nonneg hlog (by norm_num only))]
  have hq : 0 < r ^ 2 / t ^ 2 := div_pos (sq_pos_of_pos hr) (sq_pos_of_pos ht)
  have hl := Real.log_le_sub_one_of_pos hq
  rw [Real.log_div (ne_of_gt (sq_pos_of_pos hr)) (ne_of_gt (sq_pos_of_pos ht)), Real.log_pow,
    Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hx : r ^ 2 / t ^ 2 - 1 ≤ 16 / t ^ 2 := by
    apply (sub_le_iff_le_add).2
    apply (div_le_iff₀ (sq_pos_of_pos ht)).2
    have h : (16 / t ^ 2 + 1) * t ^ 2 = t ^ 2 + 16 := by
      field_simp
      ring
    rw [h]
    exact hs
  have he : 16 / t ^ 2 = 4 * (4 / t ^ 2) := by ring
  linarith only [hl, hx, he]

/-- For positive height and offsets from zero to 3/2, the shifted gamma
logarithm differs from its height-only center by at most 4/t². The squared
norm has horizontal part between 5/2 and 4. -/
theorem horizontal_shifted_log_bound {t u : ℝ} (ht : 0 < t) (hu : u ∈ Set.Icc (0 : ℝ) (3 / 2)) :
    |(Real.log ‖(((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1)‖ - Real.log Real.pi) / 2 -
          Real.log (t / (2 * Real.pi)) / 2| ≤
      4 / t ^ 2 := by
  let z : ℂ := (((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1)
  let r : ℝ := 2 * ‖z‖
  have hr0 : 0 ≤ r := mul_nonneg (by norm_num only) (norm_nonneg z)
  have hsq : r ^ 2 = (u + 5 / 2) ^ 2 + t ^ 2 := by
    dsimp only [r]
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [z, Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add]
    ring
  have htr : t ≤ r := by
    have h := sq_nonneg (u + 5 / 2)
    nlinarith only [hsq, h, ht, hr0]
  have hs : r ^ 2 ≤ t ^ 2 + 16 := by nlinarith only [hsq, hu.1, hu.2]
  have h := log_radius_error ht htr hs
  have hz : 0 < ‖z‖ := by
    dsimp only [r] at htr
    nlinarith only [ht, htr]
  have hp : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  rw [Real.log_div ht.ne' hp.ne', Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  have hl : Real.log r = Real.log 2 + Real.log ‖z‖ := by
    exact Real.log_mul (by norm_num only) hz.ne'
  rw [hl] at h
  change
    |(Real.log ‖z‖ - Real.log Real.pi) / 2 - (Real.log t - (Real.log 2 + Real.log Real.pi)) / 2| ≤
      4 / t ^ 2
  have he :
    (Real.log ‖z‖ - Real.log Real.pi) / 2 - (Real.log t - (Real.log 2 + Real.log Real.pi)) / 2 =
      (Real.log 2 + Real.log ‖z‖ - Real.log t) / 2 := by
    ring
  rw [he]
  exact h

/-- Under RH and at height at least 100, the quadratic comparison for the
shifted logarithm supplies the completion error 81/20 in the horizontal
zeta integral. The endpoint zeta terms remain explicit for later bounds. -/
theorem horizontal_logZeta_lower_of_log100 (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hQ :
      ∀ u ∈ Set.Icc (0 : ℝ) (3 / 2),
        |(Real.log ‖(((((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) + 1)‖ - Real.log Real.pi) /
                2 -
              Real.log (t / (2 * Real.pi)) / 2| ≤
          4 / t ^ 2) :
    let s : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
    (3 / 2 : ℝ) * Real.log ‖riemannZeta s‖ - (9 / 4 : ℝ) * (logDeriv riemannZeta s).re -
        (9 / 16 : ℝ) * Real.log (t / (2 * Real.pi)) -
        2187 / 160 ≤
      ∫ u in (0 : ℝ)..(3 / 2 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have ht0 : 0 < t := by linarith only [ht]
  have h :=
    horizontal_logZeta_lower_of_log_bound hRH ht0.ne' (show (0 : ℝ) < 3 / 2 by norm_num only) hQ
  have he := completion_error_le_81_20 ht
  rw [abs_of_pos ht0] at h
  dsimp only at h ⊢
  norm_num only at h
  nlinarith only [h, he]

/-- Under RH and at height at least 100, the horizontal zeta logarithmic
integral from the critical line to real part two has an explicit lower
bound in terms of the zeta endpoint. The completion-factor error is bounded
internally using the shifted gamma logarithm and the digamma estimate. -/
theorem horizontal_logZeta_lower_100 (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t) :
    let s : ℂ := ((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
    (3 / 2 : ℝ) * Real.log ‖riemannZeta s‖ - (9 / 4 : ℝ) * (logDeriv riemannZeta s).re -
        (9 / 16 : ℝ) * Real.log (t / (2 * Real.pi)) -
        2187 / 160 ≤
      ∫ u in (0 : ℝ)..(3 / 2 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  apply horizontal_logZeta_lower_of_log100 hRH ht
  intro u hu
  exact horizontal_shifted_log_bound (by linarith only [ht]) hu

/-- At real part two, the zeta logarithmic derivative has norm at most one,
uniformly in height. The explicit Euler-ratio bound at shift one evaluates
exactly to one; no zero enumeration or RH assumption is needed. -/
theorem norm_logDeriv_zeta_two_le_one (t : ℝ) :
    ‖logDeriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 := by
  have h :=
    DirichletLFunction.norm_L_logDeriv_le_euler_ratio (1 : DirichletCharacter ℂ 1) (r := 1)
      (by norm_num only) t
  norm_num only [inv_one, one_pow, one_add_one_eq_two, Real.rpow_neg, Real.rpow_one, one_div,
    div_one, DirichletCharacter.LFunction_modOne_eq] at h
  exact h

/-- Under RH at height at least 100, the finite horizontal zeta logarithmic
integral is bounded below by its right endpoint logarithm and explicit
constants. The zeta logarithmic derivative is bounded internally by one. -/
theorem horizontal_logZeta_lower_endpoint (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t) :
    (3 / 2 : ℝ) * Real.log ‖riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ -
        (9 / 16 : ℝ) * Real.log (t / (2 * Real.pi)) -
        2547 / 160 ≤
      ∫ u in (0 : ℝ)..(3 / 2 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have h := horizontal_logZeta_lower_100 hRH ht
  have hd :=
    (Complex.re_le_norm (logDeriv riemannZeta (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))).trans
      (norm_logDeriv_zeta_two_le_one t)
  dsimp only at h
  linarith only [h, hd]

/-- For real part at least 3/2, the logarithm of the zeta norm is at least
minus 9/5. The reciprocal-series lower bound and the elementary logarithm
inequality give a uniform bound without RH or a zero table. -/
theorem log_norm_zeta_ge_neg_nine_fifths {s : ℂ} (hs : (3 / 2 : ℝ) ≤ s.re) :
    -(9 / 5 : ℝ) ≤ Real.log ‖riemannZeta s‖ := by
  have hn := RiemannZeta.five_fourteenths_le_norm_zeta hs
  have hl := Real.log_le_log (show (0 : ℝ) < 5 / 14 by norm_num only) hn
  have hv := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 14 / 5 by norm_num only)
  have he : (5 / 14 : ℝ) = (14 / 5 : ℝ)⁻¹ := by norm_num only
  rw [he, Real.log_inv] at hl
  linarith only [hl, hv]

/-- Under RH and at height at least 100, the finite horizontal zeta
logarithmic integral has an explicit lower bound depending only on height.
The right endpoint is bounded using the reciprocal Dirichlet series. -/
theorem horizontal_logZeta_lower_explicit (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t) :
    -(9 / 16 : ℝ) * Real.log (t / (2 * Real.pi)) - 2979 / 160 ≤
      ∫ u in (0 : ℝ)..(3 / 2 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have h := horizontal_logZeta_lower_endpoint hRH ht
  have hn :=
    log_norm_zeta_ge_neg_nine_fifths (s := (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        norm_num only)
  linarith only [h, hn]

/-- Under RH and at height at least 100, the finite horizontal zeta
logarithmic integral exceeds minus 19 minus 9/16 times the height logarithm.
The positive logarithm of 2π is discarded from the sharper endpoint bound. -/
theorem horizontal_logZeta_lower_coarse (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t) :
    -(19 : ℝ) - (9 / 16 : ℝ) * Real.log t ≤
      ∫ u in (0 : ℝ)..(3 / 2 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have ht0 : 0 < t := by linarith only [ht]
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by
    have h := Real.pi_gt_three
    linarith only [h]
  have hl := Real.log_nonneg hpi
  have h := horizontal_logZeta_lower_explicit hRH ht
  rw [Real.log_div ht0.ne' hp.ne'] at h
  linarith only [h, hl]

/-- In the absolute-convergence half-plane, the absolute logarithmic norm
of zeta is bounded by the logarithm of zeta at the real part. This is the
pointwise majorant needed for the right-hand horizontal integral tail. -/
theorem abs_log_norm_zeta_le_real {s : ℂ} (hs : 1 < s.re) :
    |Real.log ‖riemannZeta s‖| ≤ Real.log (riemannZeta (s.re : ℂ)).re := by
  rw [← RiemannZeta.exp_backlundZetaLog hs, Complex.norm_exp, Real.log_exp]
  exact (Complex.abs_re_le_norm _).trans (RiemannZeta.norm_backlundZetaLog_le hs)

/-- Under RH, a two-unit absolute budget and integrability on the right
tail extend the finite horizontal lower bound to the whole positive
offset half-line. The finite portion is integrable even at zero heights of
zeta, and the tail is joined without changing endpoint conventions. -/
theorem horizontal_logZeta_lower_of_tail (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hTail :
      MeasureTheory.IntegrableOn
        (fun u : ℝ ↦ Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
        (Set.Ioi (3 / 2 : ℝ)))
    (hBound :
      |∫ u in Set.Ioi (3 / 2 : ℝ),
            Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖| ≤
        2) :
    -(21 : ℝ) - (9 / 16 : ℝ) * Real.log t ≤
      ∫ u in Set.Ioi (0 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith only [ht]).ne'
  have hb : (0 : ℝ) ≤ 3 / 2 := by norm_num only
  have hfinite := intervalIntegrable_horizontal_logZeta hRH ht0 hb
  have htotal := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp hfinite).union hTail
  rw [Set.Ioc_union_Ioi_eq_Ioi hb] at htotal
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi htotal hb
  have hlo := (abs_le.mp hBound).1
  have hfinitebound := horizontal_logZeta_lower_coarse hRH ht
  linarith only [hsplit, hlo, hfinitebound]

/-- Integrability of the real-axis zeta logarithm on the right tail implies
integrability at any fixed height. The zeta logarithmic norm is continuous
there, and its absolute value is dominated by the real-axis majorant. -/
theorem integrable_horizontal_tail_of_real (t : ℝ)
    (hMajor :
      MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re)
        (Set.Ioi (3 / 2 : ℝ))) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      (Set.Ioi (3 / 2 : ℝ)) := by
  have hc :
    ContinuousOn (fun u : ℝ ↦ Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      (Set.Ioi (3 / 2 : ℝ)) := by
    intro u hu
    change (3 / 2 : ℝ) < u at hu
    let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    have hs : 1 < s.re := by
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith only [hu]
    have hs1 : s ≠ 1 := fun h ↦ by
      rw [h, Complex.one_re] at hs
      exact lt_irrefl _ hs
    have hz := riemannZeta_ne_zero_of_one_lt_re hs
    have hlin : ContinuousAt (fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u :=
      ((Complex.continuous_ofReal.comp (continuous_const.add continuous_id)).add
          continuous_const).continuousAt
    have hf :
      ContinuousAt (fun v : ℝ ↦ riemannZeta (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)) u :=
      ContinuousAt.comp (f := fun v : ℝ ↦ (((1 / 2 + v : ℝ) : ℂ) + (t : ℂ) * Complex.I))
        (differentiableAt_riemannZeta hs1).continuousAt hlin
    exact ((hf.norm).log (norm_ne_zero_iff.mpr hz)).continuousWithinAt
  apply hMajor.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  change (3 / 2 : ℝ) < u at hu
  have hs : 1 < (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu]
  simpa only [Real.norm_eq_abs, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using
    abs_log_norm_zeta_le_real hs

/-- Under RH, an integrable real-axis zeta logarithm with tail integral at
most two supplies the full horizontal lower bound. The Euler logarithm
dominates the absolute value of the complex-height tail pointwise. -/
theorem horizontal_logZeta_lower_of_real_tail (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hTail :
      MeasureTheory.IntegrableOn
        (fun u : ℝ ↦ Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
        (Set.Ioi (3 / 2 : ℝ)))
    (hMajor :
      MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re)
        (Set.Ioi (3 / 2 : ℝ)))
    (hBound : (∫ u in Set.Ioi (3 / 2 : ℝ), Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re) ≤ 2) :
    -(21 : ℝ) - (9 / 16 : ℝ) * Real.log t ≤
      ∫ u in Set.Ioi (0 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  apply horizontal_logZeta_lower_of_tail hRH ht hTail
  apply (MeasureTheory.abs_integral_le_integral_abs).trans
  apply (MeasureTheory.integral_mono_ae hTail.abs hMajor ?_).trans hBound
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  change (3 / 2 : ℝ) < u at hu
  have hs : 1 < (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu]
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using abs_log_norm_zeta_le_real hs

/-- Under RH, a two-unit integral bound for the real-axis zeta logarithm
alone yields the full horizontal lower bound at height at least 100.
Continuity and Euler-log domination supply complex-tail integrability. -/
theorem horizontal_logZeta_lower_of_real_integral (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t)
    (hMajor :
      MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re)
        (Set.Ioi (3 / 2 : ℝ)))
    (hBound : (∫ u in Set.Ioi (3 / 2 : ℝ), Real.log (riemannZeta (((1 / 2 + u : ℝ) : ℂ))).re) ≤ 2) :
    -(21 : ℝ) - (9 / 16 : ℝ) * Real.log t ≤
      ∫ u in Set.Ioi (0 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  exact
    horizontal_logZeta_lower_of_real_tail hRH ht (integrable_horizontal_tail_of_real t hMajor)
      hMajor hBound

/-- Under RH and at height at least 100, the full horizontal logarithmic
zeta integral is at least `-21 - (9/16) log t`. The real-axis tail is
integrable and its integral is bounded by an explicit exponential majorant. -/
theorem horizontal_logZeta_lower_global (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t) :
    -(21 : ℝ) - (9 / 16 : ℝ) * Real.log t ≤
      ∫ u in Set.Ioi (0 : ℝ),
        Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
  exact
    horizontal_logZeta_lower_of_real_integral hRH ht RiemannZeta.integrable_log_zeta_real_tail
      RiemannZeta.integral_log_zeta_real_tail_le_two

/-- At height at least 100 and offset between zero and 3/2, the logarithmic
zeta norm is bounded by log t plus 1/100. The strip bound covers real part
up to 3/2 and the absolutely convergent series covers the remaining part. -/
theorem horizontal_logZeta_point_upper {t u : ℝ} (ht : 100 ≤ t) (hu : u ∈ Set.Icc (0 : ℝ) (3 / 2)) :
    Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      Real.log t + 1 / 100 := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have ht0 : 0 < t := by linarith only [ht]
  have hsre : s.re = 1 / 2 + u := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : s.im = t := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hsq : (0 : ℝ) < (t - 2) ^ 2 := sq_pos_of_pos (by linarith only [ht])
  have he : (0 : ℝ) ≤ 6 / (t - 2) ^ 2 := div_nonneg (by norm_num only) hsq.le
  have he2 : 6 / (t - 2) ^ 2 ≤ 1 / 100 := by
    apply (div_le_iff₀ hsq).2
    nlinarith only [ht]
  have hn : ‖riemannZeta s‖ ≤ t * Real.exp (6 / (t - 2) ^ 2) := by
    by_cases hstrip : s.re ≤ 3 / 2
    · apply
        RiemannZeta.norm_zeta_le_height (by linarith only [ht])
          (by
            rw [hsre]; linarith only [hu.1])
          hstrip
      · rw [hsim, abs_of_pos ht0]
        linarith only
      · rw [hsim, abs_of_pos ht0]
        linarith only
    · have hh := RiemannZeta.norm_zeta_lt_fourteen_fifths (s := s) (le_of_not_ge hstrip)
      have hexp : 1 ≤ Real.exp (6 / (t - 2) ^ 2) := Real.one_le_exp he
      have hm := mul_le_mul_of_nonneg_left hexp ht0.le
      linarith only [hh, ht, hm]
  by_cases hz : ‖riemannZeta s‖ = 0
  · rw [hz, Real.log_zero]
    have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht])
    linarith only [hl]
  · have hp : 0 < ‖riemannZeta s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hl := Real.log_le_log hp hn
    rw [Real.log_mul ht0.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
    linarith only [hl, he2]

/-- At any height, the absolute right-tail integral of the horizontal
zeta logarithmic norm is at most two. The real-axis Euler logarithm is an
integrable pointwise majorant with the same integral budget. -/
theorem abs_horizontal_logZeta_tail_le_two (t : ℝ) :
    |∫ u in Set.Ioi (3 / 2 : ℝ),
          Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖| ≤
      2 := by
  have hi := integrable_horizontal_tail_of_real t RiemannZeta.integrable_log_zeta_real_tail
  apply (MeasureTheory.abs_integral_le_integral_abs).trans
  apply
    (MeasureTheory.integral_mono_ae hi.abs RiemannZeta.integrable_log_zeta_real_tail ?_).trans
      RiemannZeta.integral_log_zeta_real_tail_le_two
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  change (3 / 2 : ℝ) < u at hu
  have hs : 1 < (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hu]
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using abs_log_norm_zeta_le_real hs

/-- Under RH and at height at least 100, the full horizontal zeta
logarithmic integral is at most 3 + (3/2) log t. Integrate the strip bound
and add the absolute tail budget two. -/
theorem horizontal_logZeta_upper_global (hRH : RiemannHypothesis) {t : ℝ} (ht : 100 ≤ t) :
    (∫ u in Set.Ioi (0 : ℝ), Real.log ‖riemannZeta (((1 / 2 + u : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      3 + (3 / 2 : ℝ) * Real.log t := by
  have ht0 : t ≠ 0 := (show (0 : ℝ) < t by linarith only [ht]).ne'
  have hb : (0 : ℝ) ≤ 3 / 2 := by norm_num only
  have hfinite := intervalIntegrable_horizontal_logZeta hRH ht0 hb
  have htail := integrable_horizontal_tail_of_real t RiemannZeta.integrable_log_zeta_real_tail
  have htotal := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb).mp hfinite).union htail
  rw [Set.Ioc_union_Ioi_eq_Ioi hb] at htotal
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi htotal hb
  have hpoint :=
    intervalIntegral.integral_mono_on hb hfinite intervalIntegrable_const
      (fun u hu ↦ horizontal_logZeta_point_upper ht hu)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hpoint
  have htailbound := (abs_le.mp (abs_horizontal_logZeta_tail_le_two t)).2
  linarith only [hsplit, hpoint, htailbound]

/-- Under RH, the difference of the full horizontal zeta logarithmic
integrals at ordered heights at least 100 is bounded by
`24 + (33/16) log v`. Combine the upper and lower bounds at both heights. -/
theorem abs_horizontal_logZeta_diff_le (hRH : RiemannHypothesis) {u v : ℝ} (hu : 100 ≤ u)
    (huv : u ≤ v) :
    |(∫ x in Set.Ioi (0 : ℝ),
            Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖) -
          (∫ x in Set.Ioi (0 : ℝ),
            Real.log ‖riemannZeta (((1 / 2 + x : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖)| ≤
      24 + (33 / 16 : ℝ) * Real.log v := by
  have hv : 100 ≤ v := hu.trans huv
  have hlU := horizontal_logZeta_lower_global hRH hu
  have hlV := horizontal_logZeta_lower_global hRH hv
  have hhU := horizontal_logZeta_upper_global hRH hu
  have hhV := horizontal_logZeta_upper_global hRH hv
  have hlog := Real.log_le_log (show (0 : ℝ) < u by linarith only [hu]) huv
  apply abs_le.mpr
  constructor <;> linarith only [hlU, hlV, hhU, hhV, hlog]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
