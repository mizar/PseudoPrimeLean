/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiSqrtToLeeNosal

/-! # Finite square-root certificate connected to the Lee–Nosal envelope -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The square-root certificate on `[1423, 1000000]` implies the Lee–Nosal psi
bound on that interval. Both the finite certificate and the comparison are
unconditional. -/
theorem psi_lee_nosal_1423_million {x : ℝ} (ha : 1423 ≤ x) (hb : x ≤ 1000000) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) := by
  exact psi_lee_nosal_of_1423 ha (Arithmetic.psi_four_fifths_1423_million ha hb)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
