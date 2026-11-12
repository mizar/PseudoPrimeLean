/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta10000
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta10000to11287
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta11287to12035
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta12035to12995
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta12995to14251
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta14251to15058
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta15058to16384

/-! # Cumulative Lee–Nosal theta bound through 16384 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent theta certificates give the Lee–Nosal estimate on `[2657, 16384)`. -/
theorem theta_lee_nosal_2657_16384 {x : ℝ} (ha : 2657 ≤ x) (hb : x < 16384) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h0 : x < 10000
  · exact theta_lee_nosal_2657_10000 ha h0
  by_cases h1 : x < 11287
  · exact theta_lee_nosal_10000_11287 (le_of_not_gt h0) h1
  by_cases h2 : x < 12035
  · exact theta_lee_nosal_11287_12035 (le_of_not_gt h1) h2
  by_cases h3 : x < 12995
  · exact theta_lee_nosal_12035_12995 (le_of_not_gt h2) h3
  by_cases h4 : x < 14251
  · exact theta_lee_nosal_12995_14251 (le_of_not_gt h3) h4
  by_cases h5 : x < 15058
  · exact theta_lee_nosal_14251_15058 (le_of_not_gt h4) h5
  · exact theta_lee_nosal_15058_16384 (le_of_not_gt h5) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
