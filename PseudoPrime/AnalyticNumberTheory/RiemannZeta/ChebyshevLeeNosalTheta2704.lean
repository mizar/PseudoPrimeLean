/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta2657to2667
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta2667to2704

/-! # Cumulative Lee–Nosal theta bound through 2704 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 2704)`. -/
theorem theta_lee_nosal_2657_2704 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 2704) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 2667
  · exact theta_lee_nosal_2657_2667 ha h
  · exact theta_lee_nosal_2667_2704 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
