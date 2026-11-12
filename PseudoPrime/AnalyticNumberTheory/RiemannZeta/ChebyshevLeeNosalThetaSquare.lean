/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalSquare
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta50000

/-! # Finite theta square-logarithmic bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `2657 ≤ x ≤ 50000`, the Chebyshev theta error is at most
`sqrt x * log x ^ 2 / 12`. The certified Lee–Nosal interval gives the sharper input. -/
theorem theta_error_square_twelve_finite {x : ℝ} (ha : 2657 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.theta x - x| ≤ Real.sqrt x * (Real.log x ^ 2 / 12) := by
  have hx : Real.exp 1 ≤ x := Real.exp_one_lt_three.le.trans (by linarith only [ha])
  exact (theta_lee_nosal_2657_50000 ha hb).trans (lee_nosal_le_square_twelve hx)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
