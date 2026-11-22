/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Million
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.Psi94Low11To17

/-! # The unconditional Chebyshev psi bound with coefficient 47/50 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For every real `x` in `[11, 1000000]`, the normalized psi error is at most `47 / 50`.
The small interval uses an internal LCM certificate. From 17 onward, the stronger
coefficient `81 / 100` suffices. This theorem exposes only the real inequality. -/
theorem psi94_million {x : ℝ} (hx : 11 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (47 / 50 : ℝ) := by
  by_cases h : x < 17
  · exact Cert.Chebyshev.PsiSqrtBound.psi94_on_11_17 hx h
  · exact (psi81_million (le_of_not_gt h) hx').trans (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
