/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLeeNosal101to108

/-! # A certified Lee–Nosal endpoint at 101 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At `x = 101`, the unconditional Lee–Nosal psi error bound follows from the
least-common-multiple certificate and the rational envelope bound. -/
theorem psi_lee_nosal_101 :
    |Chebyshev.psi 101 - 101| ≤
      Real.sqrt 101 *
        (Real.log 101 * (Real.log 101 - Real.log (Real.log 101)) / (8 * Real.pi)) := by
  exact psi_lee_nosal_101_108 (by norm_num only) (by norm_num only)

/-- The Lee–Nosal psi error bound holds unconditionally on `[101, 103]`.
The proof combines endpoint least-common-multiple checks and envelope monotonicity. -/
theorem psi_lee_nosal_101_103 {x : ℝ} (ha : 101 ≤ x) (hb : x ≤ 103) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact psi_lee_nosal_101_108 ha (hb.trans_lt (by norm_num only))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
