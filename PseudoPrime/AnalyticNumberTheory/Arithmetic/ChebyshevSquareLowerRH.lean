/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSquareLogLowerRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CoarseZeroCountNumerics

/-! # One-sided square-logarithmic psi bound under RH -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH, the one-sided square-logarithmic psi estimate with coefficient
`1/12` holds for `x ≥ 25000000`. The RH zero-count theorem discharges the
counting hypothesis of the explicit-formula estimate. -/
theorem psi_lower_square_twelve_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 25000000 ≤ x) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  exact
    RiemannZeta.psi_lower_square_coarse hRH hx
      (fun t ht ↦
        (RiemannZeta.positive_zero_count_budget_of_RH hRH t ht).trans
          (RiemannZeta.good_count_budget_le_log ht))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
