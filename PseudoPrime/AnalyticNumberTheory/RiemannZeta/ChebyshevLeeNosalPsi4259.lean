/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi2687
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal2687to4259

/-! # Cumulative Lee–Nosal psi bound through 4259 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 4259)`. -/
theorem psi_lee_nosal_101_4259 {x : ℝ} (ha : 101 ≤ x) (hb : x < 4259) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 2687
  · exact psi_lee_nosal_101_2687 ha h
  · exact psi_lee_nosal_2687_4259 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
