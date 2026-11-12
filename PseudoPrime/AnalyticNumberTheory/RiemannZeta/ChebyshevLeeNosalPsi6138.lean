/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi4259
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal4259to6138

/-! # Cumulative Lee–Nosal psi bound through 6138 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 6138)`. -/
theorem psi_lee_nosal_101_6138 {x : ℝ} (ha : 101 ≤ x) (hb : x < 6138) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 4259
  · exact psi_lee_nosal_101_4259 ha h
  · exact psi_lee_nosal_4259_6138 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
