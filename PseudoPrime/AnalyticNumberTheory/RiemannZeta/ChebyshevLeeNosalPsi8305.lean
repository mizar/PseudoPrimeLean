/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi6138
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal6138to8305

/-! # Cumulative Lee–Nosal psi bound through 8305 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 8305)`. -/
theorem psi_lee_nosal_101_8305 {x : ℝ} (ha : 101 ≤ x) (hb : x < 8305) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 6138
  · exact psi_lee_nosal_101_6138 ha h
  · exact psi_lee_nosal_6138_8305 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
