/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsiSquare

/-! # A square-logarithmic Chebyshev bound under RH -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the psi error is bounded by `sqrt x * log x ^ 2 / 12` for every
`x ≥ 101`. Combine the unconditional finite certificate with the explicit-formula
estimate on the half-line beginning at `50000`. -/
theorem psi_error_square_from_101_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x * (Real.log x ^ 2 / 12) := by
  by_cases h : x ≤ 50000
  · exact psi_error_square_twelve_finite hx h
  · exact psi_error_square_twelve_of_RH hRH (le_of_not_ge h)

/-- Under RH, `ψ(x)` is at least `x - sqrt(x) * log(x)^2 / 12` for every
`x ≥ 101`. This is the lower half of the absolute-error bound and extends
the one-sided estimate available from the large-scale explicit formula. -/
theorem psi_lower_square_from_101_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x := by
  have h := (abs_le.mp (psi_error_square_from_101_of_RH hRH hx)).1
  nlinarith only [h]

/-- Under RH, `ψ(x)` is at most `x + sqrt(x) * log(x)^2 / 12` for every
`x ≥ 101`. This is the upper half of the absolute-error bound. -/
theorem psi_upper_square_from_101_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    Chebyshev.psi x ≤ x + (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 := by
  have h := (abs_le.mp (psi_error_square_from_101_of_RH hRH hx)).2
  nlinarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
