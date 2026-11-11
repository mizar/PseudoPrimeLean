/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundRealPhase
import PseudoPrime.Analysis.ContinuousLogDerivative

/-! # Euler-normalized xi argument on the right vertical line -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The complex Euler-normalized logarithm of twice xi along the right
vertical line. Its imaginary part is the vertical-edge phase. -/
noncomputable def xiVerticalLog (y : ℝ) : ℂ :=
  AnalyticNumberTheory.RiemannXi.xiLogFactor (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) +
    AnalyticNumberTheory.RiemannZeta.backlundZetaLog (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)

private theorem vertical_log_cont (y : ℝ) : ContinuousAt xiVerticalLog y := by
  let s : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I
  have hs : s.re = 3 / 2 := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hcut : s - 1 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.sub_re, Complex.one_re, hs]
    norm_num only
  have ha :=
    AnalyticNumberTheory.RiemannXi.differentiableAt_xiLogFactor
      (by
        rw [hs]; norm_num only)
      hcut
  have hb :=
    AnalyticNumberTheory.RiemannZeta.differentiableAt_backlundZetaLog (s := s)
      (by
        rw [hs]; norm_num only)
  have hc : ContinuousAt (fun v : ℝ ↦ ((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) y :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  exact
    ContinuousAt.comp (f := fun v : ℝ ↦ ((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
      (ha.add hb).continuousAt hc

private theorem vertical_xi_deriv (y : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦
        2 * AnalyticNumberTheory.RiemannXi.riemannXi (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I))
      (2 *
        (deriv AnalyticNumberTheory.RiemannXi.riemannXi (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
          Complex.I))
      y := by
  let s : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I
  have hp : HasDerivAt (fun v : ℂ ↦ ((3 / 2 : ℝ) : ℂ) + v * Complex.I) Complex.I y := by
    simpa only [one_mul, id_eq] using
      (((hasDerivAt_id (y : ℂ)).mul_const Complex.I).const_add (((3 / 2 : ℝ) : ℂ)))
  have hd := (AnalyticNumberTheory.RiemannXi.differentiable_riemannXi s).hasDerivAt.comp (y : ℂ) hp
  have hr := hd.comp_ofReal
  simpa only [Function.comp_def, id_eq, s] using hr.const_mul (2 : ℂ)

/-- The imaginary part of the vertical Euler-normalized xi logarithm has
derivative equal to the real part of xi's logarithmic derivative. The
continuous-logarithm derivative theorem cancels the positive factor two. -/
theorem xi_vertical_arg_deriv (y : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (xiVerticalLog v).im)
      (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi
          (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re
      y := by
  let f : ℝ → ℂ := fun v ↦
    2 * AnalyticNumberTheory.RiemannXi.riemannXi (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I)
  have he : ∀ v ∈ (Set.univ : Set ℝ), Complex.exp (xiVerticalLog v) = f v := by
    intro v hv
    apply exp_xi_euler_log
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  have hg :=
    Analysis.hasDerivWithinAt_continuous_log (Set.mem_univ y)
      (vertical_log_cont y).continuousWithinAt (vertical_xi_deriv y).hasDerivWithinAt he
  have hg' := hg.hasDerivAt Filter.univ_mem
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hg'
  have hratio (v : ℝ) :
    (2 *
          (deriv AnalyticNumberTheory.RiemannXi.riemannXi
              (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) *
            Complex.I)) /
        f v =
      logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) *
        Complex.I := by
    dsimp only [f]
    rw [mul_div_mul_left _ _ (by norm_num only : (2 : ℂ) ≠ 0), logDeriv_apply]
    ring
  dsimp only [f] at hratio
  simpa only [Function.comp_def, Complex.imCLM_apply, hratio, Complex.mul_I_im] using hi

/-- The right vertical-edge integral of the real logarithmic derivative of
xi equals the Euler-normalized vertical phase at height `t`. The phase at
height zero vanishes, and the zero-free line provides integrability. -/
theorem xi_vertical_arg_integral (t : ℝ) :
    (∫ y in (0 : ℝ)..t,
        (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi
            (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re) =
      (xiVerticalLog t).im := by
  have hf :
    Continuous
      (fun y : ℝ ↦
        logDeriv AnalyticNumberTheory.RiemannXi.riemannXi
          (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    let s : ℂ := ((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I
    have hne : AnalyticNumberTheory.RiemannXi.riemannXi s ≠ 0 := by
      apply AnalyticNumberTheory.RiemannXi.riemannXi_ne_zero_of_one_lt_re
      simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero]
      norm_num only
    have hd :=
      (((AnalyticNumberTheory.RiemannXi.differentiable_riemannXi.analyticAt s).deriv).div
          (AnalyticNumberTheory.RiemannXi.differentiable_riemannXi.analyticAt s) hne).continuousAt
    change ContinuousAt (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi) s at hd
    have hc : ContinuousAt (fun v : ℝ ↦ ((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) y :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    exact ContinuousAt.comp (f := fun v : ℝ ↦ ((3 / 2 : ℝ) : ℂ) + (v : ℂ) * Complex.I) hd hc
  have hint :
    IntervalIntegrable
      (fun y : ℝ ↦
        (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi
            (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).re)
      MeasureTheory.volume 0 t :=
    (Complex.continuous_re.comp hf).intervalIntegrable 0 t
  have he : (xiVerticalLog 0).im = 0 := by
    simpa only [xiVerticalLog, Complex.ofReal_zero, zero_mul, add_zero] using
      (xi_euler_log_im_ofReal (x := 3 / 2) (by norm_num only))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ ↦ xi_vertical_arg_deriv y) hint, he,
    sub_zero]

end PseudoPrime.PrimeTestBounds.MillerRabin
