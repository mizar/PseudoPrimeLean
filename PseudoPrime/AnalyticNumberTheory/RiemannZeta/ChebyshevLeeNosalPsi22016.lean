/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi17761
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal17761to22016

/-! # Cumulative Lee–Nosal psi bound through 22016 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 22016)`. -/
theorem psi_lee_nosal_101_22016 {x : ℝ} (ha : 101 ≤ x) (hb : x < 22016) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 17761
  · exact psi_lee_nosal_101_17761 ha h
  · exact psi_lee_nosal_17761_22016 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
