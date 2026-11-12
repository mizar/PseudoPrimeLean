/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogMain265RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogGap265

/-! # Lee–Nosal psi error bound from logarithmic height twenty-six and one half -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and `L ≥ 53/2`, the psi error at `exp L` is at most the
Lee–Nosal envelope. Combine the explicit main-term bound with the certified
comparison to the envelope. -/
theorem psi_lee_nosal_exp265_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      Real.exp (L / 2) * (L * (L - Real.log L) / (8 * Real.pi)) := by
  have h := (psi_error_main265_of_RH hRH hL).trans (chebyshev_main_le_envelope265 hL)
  have hp := Real.exp_pos (L / 2)
  have hm := (div_le_iff₀ hp).1 h
  nlinarith only [hm]

/-- Under RH, the Lee–Nosal psi error estimate holds for every positive `x`
with `log x ≥ 53/2`. Substitution in the exponential-scale result gives the
bound on the original variable. -/
theorem psi_lee_nosal_log265_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : (53 / 2 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have h := psi_lee_nosal_exp265_of_RH hRH hL
  have hs : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [Real.exp_log hx, hs] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
