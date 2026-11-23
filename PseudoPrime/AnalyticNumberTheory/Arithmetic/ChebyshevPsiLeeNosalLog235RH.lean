/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogMain235RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogRemainderBounds235
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalLogGap235

/-! # Lee–Nosal psi error bound from logarithmic height 23.5 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH and `L ≥ 47/2`, the normalized psi error stays at least `1/200`
below the Lee–Nosal envelope. The sharp main term, certified `1/500`
remainder, and envelope comparison provide the explicit margin. -/
theorem psi_lee_nosal_margin235_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) + 1 / 200 ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
  have hm := RiemannZeta.psi_error_main_remainder235 hRH hL
  have hr := RiemannZeta.scale235_remainder_le hL
  have hg := RiemannZeta.chebyshev_main_le_envelope235 hL
  dsimp only at hm hr
  linarith only [hm, hr, hg]

/-- Under RH and `L ≥ 47/2`, the psi error at `exp L` is at most the
Lee–Nosal envelope. Multiply the normalized bound by the positive square-root
scale after discarding the explicit margin. -/
theorem psi_lee_nosal_exp235_of_RH (hRH : RiemannHypothesis) {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      Real.exp (L / 2) * (L * (L - Real.log L) / (8 * Real.pi)) := by
  have h := psi_lee_nosal_margin235_of_RH hRH hL
  have h' :
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      L * (L - Real.log L) / (8 * Real.pi) := by
    linarith only [h]
  have h'' := (div_le_iff₀ (Real.exp_pos (L / 2))).1 h'
  simpa only [mul_comm] using h''

/-- Under RH, the Lee–Nosal psi error estimate holds for every positive `x`
with `log x ≥ 47/2`. Substitute `L = log x` in the exponential-scale bound. -/
theorem psi_lee_nosal_log235_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : (47 / 2 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  have h := psi_lee_nosal_exp235_of_RH hRH hL
  rw [Real.exp_half, Real.exp_log hx] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
