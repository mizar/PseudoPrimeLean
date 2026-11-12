/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalTheta32768to39760
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosalThetaThrough50000

/-! # Lee–Nosal theta error bound from 32768 to 50000 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Lee–Nosal theta error bound holds unconditionally on `[32768, 50000]`.
Two independently proved interval theorems cover the full range. -/
theorem theta_lee_nosal_32768_50000 {x : ℝ} (ha : 32768 ≤ x) (hb : x ≤ 50000) :
    |Chebyshev.theta x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x ≤ 39760
  · exact theta_lee_nosal_32768_39760 ha h
  · exact theta_lee_nosal_39760_50000 (le_of_not_ge h) hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
