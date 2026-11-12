/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta3479
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta3479to3600
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta3600to4225

/-! # Cumulative Lee–Nosal theta bound through 4225 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 4225)`. -/
theorem theta_lee_nosal_2657_4225 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 4225) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h1 : x < 3479
  · exact theta_lee_nosal_2657_3479 ha h1
  by_cases h2 : x < 3600
  · exact theta_lee_nosal_3479_3600 (le_of_not_gt h1) h2
  · exact theta_lee_nosal_3600_4225 (le_of_not_gt h2) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
