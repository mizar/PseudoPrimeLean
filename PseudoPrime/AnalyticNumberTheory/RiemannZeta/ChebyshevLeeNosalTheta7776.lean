/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta4900
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta4900to5625
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta5625to6204
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta6204to6824
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta6824to7318
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta7318to7776

/-! # Cumulative Lee–Nosal theta bound through 7776 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 7776)`. -/
theorem theta_lee_nosal_2657_7776 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 7776) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h0 : x < 4900
  · exact theta_lee_nosal_2657_4900 ha h0
  by_cases h1 : x < 5625
  · exact theta_lee_nosal_4900_5625 (le_of_not_gt h0) h1
  by_cases h2 : x < 6204
  · exact theta_lee_nosal_5625_6204 (le_of_not_gt h1) h2
  by_cases h3 : x < 6824
  · exact theta_lee_nosal_6204_6824 (le_of_not_gt h2) h3
  by_cases h4 : x < 7318
  · exact theta_lee_nosal_6824_7318 (le_of_not_gt h3) h4
  · exact theta_lee_nosal_7318_7776 (le_of_not_gt h4) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
