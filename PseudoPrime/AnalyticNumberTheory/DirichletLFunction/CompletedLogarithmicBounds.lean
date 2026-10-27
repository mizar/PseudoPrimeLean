/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogDerivativeNumericalBounds

/-! # Explicit logarithmic bounds on the reflected fixed line

Replace linear height bounds by logarithmic bounds compatible with triangular decay.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- On Re s=17/16, every character gamma logarithmic derivative has norm
at most 12+log(4+abs(Im s))/2. Use the explicit central-strip logarithmic
estimate for heights at least one and the numerical compact-height estimate
otherwise. This is integrable against the triangular kernel's quadratic decay. -/
theorem norm_logDeriv_gammaFactor_seventeen_sixteenths_le_log {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : s.re = 17 / 16) :
    ‖logDeriv χ.gammaFactor s‖ ≤ 12 + Real.log (4 + |s.im|) / 2 := by
  have hlog : 0 ≤ Real.log (4 + |s.im|) := Real.log_nonneg (by linarith only [abs_nonneg s.im])
  by_cases ht : 1 ≤ |s.im|
  · have hsr : |s.re| ≤ 2 := by
      rw [hs]; norm_num only
    have hb := norm_logDeriv_gammaFactor_le_log χ hsr ht
    have hnlog : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
      rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi))]
      have hp := Real.log_le_sub_one_of_pos Real.pi_pos
      linarith only [hp, Real.pi_lt_four]
    linarith only [hb, hnlog, Real.pi_lt_four, Gamma.digammaLogErrorBound_le_eight]
  · have hb := norm_logDeriv_gammaFactor_seventeen_sixteenths_le χ hs
    have ht1 : |s.im| ≤ 1 := (lt_of_not_ge ht).le
    linarith only [hb, ht1, hlog]

/-- On Re s=17/16, a nonprincipal character's completed logarithmic derivative
has norm at most 284+log(4+abs t)/2. Add the ordinary inverse-gap bound 272
and the logarithmic gamma bound. No RH assumption is needed.
This supplies the explicit reflected integrand bound for the alpha-18 kernel. -/
theorem norm_logDeriv_completed_seventeen_sixteenths_le_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction (((17 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      284 + Real.log (4 + |t|) / 2 := by
  let s : ℂ := ((17 / 16 : ℝ) : ℂ) + Complex.I * t
  have hr : s.re = 17 / 16 := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = t := by
    simp only [s, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul, zero_add]
  have hr1 : 1 ≤ s.re := by
    rw [hr]; norm_num only
  have hp : 0 < s.re := zero_lt_one.trans_le hr1
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr1) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have ho := norm_logDeriv_le_inv_gap χ (by norm_num only : (1 : ℝ) < 17 / 16) t
  norm_num only at ho
  rw [mul_comm (t : ℂ) Complex.I] at ho
  have hg := norm_logDeriv_gammaFactor_seventeen_sixteenths_le_log χ hr
  rw [hi] at hg
  have hc :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [he]; ring
  change ‖logDeriv χ.completedLFunction s‖ ≤ _
  rw [hc]
  have hn := norm_add_le (logDeriv χ.LFunction s) (logDeriv χ.gammaFactor s)
  linarith only [hn, ho, hg]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
