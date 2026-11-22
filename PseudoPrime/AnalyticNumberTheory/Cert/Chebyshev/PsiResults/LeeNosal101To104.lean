/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiChecks.LeeNosal101To108

/-! # A half-open Lee–Nosal interval at the low endpoint -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiResults

/-- The Lee–Nosal psi error inequality holds unconditionally on `[101, 104)`.
The upper endpoint uses `psi 103` and the lower endpoint uses a refined lcm certificate. -/
theorem bound_101_104 {x : ℝ} (ha : 101 ≤ x) (hb : x < 104) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact PsiChecks.bound_101_108 ha (hb.trans (by norm_num only))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiResults
