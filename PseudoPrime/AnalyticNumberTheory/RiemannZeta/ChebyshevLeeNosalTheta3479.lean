/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta3292
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta3292to3479

/-! # Cumulative Lee–Nosal theta bound through 3479 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 3479)`. -/
theorem theta_lee_nosal_2657_3479 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 3479) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 3292
  · exact theta_lee_nosal_2657_3292 ha h
  · exact theta_lee_nosal_3292_3479 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
