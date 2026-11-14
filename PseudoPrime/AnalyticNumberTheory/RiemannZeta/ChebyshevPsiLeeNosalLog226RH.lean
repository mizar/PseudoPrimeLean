/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombined226RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelopeCompare226

/-! # Lee–Nosal-type ψ error above logarithmic height 22.6 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, for `x > 0` and `log x ≥ 113/5`, the Chebyshev ψ error is
below the Lee–Nosal normalized envelope with an additional `1/300` margin.
The combined zero budget and the uniform envelope comparison supply the bound. -/
theorem psi_lee_nosal_margin226_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : (113 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 1 / 300) := by
  have h := (psi_error_envelope226 hRH hL).trans (envelope226_le_target hL)
  rw [Real.exp_log hx, Real.exp_half, Real.exp_log hx] at h
  simpa only [mul_comm] using (div_le_iff₀ (Real.sqrt_pos.2 hx)).1 h

/-- Under RH, the Lee–Nosal-type ψ error estimate holds for `x > 0` and
`log x ≥ 113/5`. Discard the positive margin in the stronger estimate. -/
theorem psi_lee_nosal_log226_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : (113 / 5 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have h := psi_lee_nosal_margin226_of_RH hRH hx hL
  have hs := Real.sqrt_nonneg x
  nlinarith only [h, hs]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
