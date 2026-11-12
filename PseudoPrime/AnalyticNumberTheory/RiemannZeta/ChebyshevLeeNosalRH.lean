/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevSquareLowerRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalCoarseRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiWeakPNTMiddleRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiWeakPNTHighRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CoarseZeroCountNumerics

/-! # RH consequences of the coarse zeta zero count -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, for positive `x` with `log x ≥ 43`, the psi error lies below
the Lee–Nosal envelope with an additional `11/4 * sqrt x` of margin. The
coarse positive-height zero count is supplied by the RH counting theorem. -/
theorem psi_lee_nosal_margin_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : 43 ≤ Real.log x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 11 / 4) := by
  exact
    psi_error_envelope_of_log_coarse hRH hx hL
      (fun t ht ↦ (positive_zero_count_budget_of_RH hRH t ht).trans (good_count_budget_le_log ht))

/-- Under RH, for positive `x` with `log x ≥ 43`, the theta error lies below
the Lee–Nosal envelope with an additional `5/4 * sqrt x` of margin. The
coarse positive-height zero count is supplied by the RH counting theorem. -/
theorem theta_lee_nosal_margin_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : 43 ≤ Real.log x) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 5 / 4) := by
  exact
    theta_error_envelope_of_log_coarse hRH hx hL
      (fun t ht ↦ (positive_zero_count_budget_of_RH hRH t ht).trans (good_count_budget_le_log ht))

/-- Under RH, for every `x ≥ 50000`, the absolute psi error is at most
`sqrt x * log x ^ 2 / 12`. The finite middle range and the upper half-line
use different widths in the normalized explicit formula. -/
theorem psi_error_square_twelve_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 50000 ≤ x) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x ^ 2 / 12) := by
  by_cases h : x ≤ 1000000
  · exact
      psi_error_square_twelve_middle hRH hx h
        (fun t ht ↦ (positive_zero_count_budget_of_RH hRH t ht).trans (good_count_budget_le_log ht))
  · exact
      psi_error_square_twelve_high hRH (le_of_not_ge h)
        (fun t ht ↦ (positive_zero_count_budget_of_RH hRH t ht).trans (good_count_budget_le_log ht))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
