/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalPsi8305
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal8305to11083

/-! # Cumulative Lee–Nosal psi bound through 11083 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The adjacent psi interval certificates yield the Lee–Nosal estimate on `[101, 11083)`. -/
theorem psi_lee_nosal_101_11083 {x : ℝ} (ha : 101 ≤ x) (hb : x < 11083) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 8305
  · exact psi_lee_nosal_101_8305 ha h
  · exact psi_lee_nosal_8305_11083 (le_of_not_gt h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
