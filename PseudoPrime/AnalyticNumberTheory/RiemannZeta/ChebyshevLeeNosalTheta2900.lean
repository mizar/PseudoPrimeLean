/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta2704
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta2704to2900

/-! # Cumulative Lee–Nosal theta bound through 2900 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 2900)`. -/
theorem theta_lee_nosal_2657_2900 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 2900) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 2704
  · exact theta_lee_nosal_2657_2704 ha h
  · exact theta_lee_nosal_2704_2900 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
