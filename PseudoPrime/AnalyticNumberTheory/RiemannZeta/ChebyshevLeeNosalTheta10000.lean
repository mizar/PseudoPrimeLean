/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta7776
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta7776to8292
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta8292to8600
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta8600to8981
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta8981to9551
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta9551to10000

/-! # Cumulative Lee–Nosal theta bound through 10000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 10000)`. -/
theorem theta_lee_nosal_2657_10000 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 10000) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h0 : x < 7776
  · exact theta_lee_nosal_2657_7776 ha h0
  by_cases h1 : x < 8292
  · exact theta_lee_nosal_7776_8292 (le_of_not_gt h0) h1
  by_cases h2 : x < 8600
  · exact theta_lee_nosal_8292_8600 (le_of_not_gt h1) h2
  by_cases h3 : x < 8981
  · exact theta_lee_nosal_8600_8981 (le_of_not_gt h2) h3
  by_cases h4 : x < 9551
  · exact theta_lee_nosal_8981_9551 (le_of_not_gt h3) h4
  · exact theta_lee_nosal_9551_10000 (le_of_not_gt h4) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
