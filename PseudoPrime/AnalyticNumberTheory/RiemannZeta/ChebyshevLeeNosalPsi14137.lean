/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi11083
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal11083to14137

/-! # Cumulative Lee–Nosal psi bound through 14137 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 14137)`. -/
theorem psi_lee_nosal_101_14137 {x : ℝ} (ha : 101 ≤ x) (hb : x < 14137) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 11083
  · exact psi_lee_nosal_101_11083 ha h
  · exact psi_lee_nosal_11083_14137 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
