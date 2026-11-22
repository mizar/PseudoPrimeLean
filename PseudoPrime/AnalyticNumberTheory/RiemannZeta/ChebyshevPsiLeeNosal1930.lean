/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal327To503
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal503To1006
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal1006To1930

/-! # Lee–Nosal psi bound through 1930 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The unconditional Lee–Nosal psi bound on `[101, 1930)` follows from the
finite interval certificates. This supplies the initial range below the
square-root certificate. -/
theorem psi_lee_nosal_101_1930 {x : ℝ} (ha : 101 ≤ x) (hb : x < 1930) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  by_cases h : x < 503
  · exact Cert.Chebyshev.PsiChecks.bound_101_503 ha h
  by_cases h' : x < 1006
  · exact Cert.Chebyshev.PsiChecks.bound_503_1006 (le_of_not_gt h) h'
  · exact Cert.Chebyshev.PsiChecks.bound_1006_1930 (le_of_not_gt h') hb

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
