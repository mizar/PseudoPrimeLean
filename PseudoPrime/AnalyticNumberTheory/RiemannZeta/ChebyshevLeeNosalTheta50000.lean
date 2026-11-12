/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta32768
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta32768to50000

/-! # Cumulative Lee–Nosal theta bound through 50000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The checked intervals give the Lee–Nosal theta estimate on `[2657, 50000]`. -/
theorem theta_lee_nosal_2657_50000 {x : ℝ} (ha : 2657 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 32768
  · exact theta_lee_nosal_2657_32768 ha h
  · exact theta_lee_nosal_32768_50000 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
