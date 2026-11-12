/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogMain265RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevThetaLeeNosalLogGap36
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPrimePowers36

/-! # Lee–Nosal theta bound from logarithmic height thirty-six -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, for positive `x` with `log x ≥ 36`, the theta error is bounded
by the Lee–Nosal envelope. The psi main-term bound has enough certified
margin to absorb the prime-power excess. -/
theorem theta_lee_nosal_log36_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : 36 ≤ Real.log x) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have h265 : (53 / 2 : ℝ) ≤ Real.log x := by linarith only [hL]
  have hmain := psi_error_main265_of_RH hRH h265
  have hgap := chebyshev_main_le_envelope36 hL
  have hnorm := hmain.trans hgap
  have he := Real.exp_pos (Real.log x / 2)
  have hscale := (div_le_iff₀ he).1 hnorm
  have hs : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [Real.exp_log hx, hs] at hscale
  have hp := abs_le.mp hscale
  have hd := psi_sub_theta_36 hx (by linarith only [hL])
  have hd0 := sub_nonneg.mpr (Chebyshev.theta_le_psi x)
  have hs0 := Real.sqrt_nonneg x
  apply abs_le.mpr
  constructor
  · nlinarith only [hp.1, hd]
  · nlinarith only [hp.2, hd0, hs0]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
