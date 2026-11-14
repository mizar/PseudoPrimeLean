/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiCombined100RH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelopeRemainder20
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiEnvelope20RH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocal100Brackets

/-! # Conditional ψ error margin above logarithmic height 20 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the stated height-100 zero count and reciprocal head bound,
the Lee–Nosal normalized ψ error bound has margin `1/150` for `log x ≥ 20`.
The combined-zero smoothing envelope and its uniform comparison give the result. -/
theorem psi_lee_nosal_margin20_of_head (hRH : RiemannHypothesis) (h100 : zeroCount 100 = 58)
    (hhead : zeroReciprocalSum 100 ≤ 11846 / 10000) {x : ℝ} (hx : 0 < x)
    (hL : (20 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 1 / 150) := by
  have h := (psi_error_envelope20 hRH h100 hhead hL).trans (envelope20_le_target hL)
  rw [Real.exp_log hx, Real.exp_half, Real.exp_log hx] at h
  simpa only [mul_comm] using (div_le_iff₀ (Real.sqrt_pos.2 hx)).1 h

/-- Under RH, 29 ordered positive zeros satisfying the lower brackets and a
height-100 count upper bound give the `1/150` margin for `log x ≥ 20`.
Completeness, simplicity and the reciprocal head bound follow from the count. -/
theorem psi_lee_nosal_margin20_of_brackets (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hbrackets : LowZero100LowerBounds g) {x : ℝ} (hx : 0 < x)
    (hL : (20 : ℝ) ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 1 / 150) := by
  obtain ⟨h100, hhead⟩ := head100_of_count hRH g hmono hpos hheight hzero hcount hbrackets
  exact psi_lee_nosal_margin20_of_head hRH h100 hhead hx hL

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
