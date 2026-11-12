/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal327to503
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal503to1006
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal1006to1930
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal1930to2687

/-! # Cumulative Lee–Nosal psi bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 1006)`. -/
theorem psi_lee_nosal_101_1006 {x : ℝ} (ha : 101 ≤ x) (hb : x < 1006) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 503
  · exact psi_lee_nosal_101_503 ha h
  · exact psi_lee_nosal_503_1006 (le_of_not_gt h) hb

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 1930)`. -/
theorem psi_lee_nosal_101_1930 {x : ℝ} (ha : 101 ≤ x) (hb : x < 1930) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 1006
  · exact psi_lee_nosal_101_1006 ha h
  · exact psi_lee_nosal_1006_1930 (le_of_not_gt h) hb

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 2687)`. -/
theorem psi_lee_nosal_101_2687 {x : ℝ} (ha : 101 ≤ x) (hb : x < 2687) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 1930
  · exact psi_lee_nosal_101_1930 ha h
  · exact psi_lee_nosal_1930_2687 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
