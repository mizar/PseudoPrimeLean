/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.Bound

/-! # The Lee–Nosal bound for the Chebyshev theta function -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH, the absolute theta error divided by the square root satisfies the Lee–Nosal
bound for every real x ≥ 2657. Apply the certified two-sided estimate. -/
theorem theta_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 2657 ≤ x) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact Cert.Chebyshev.ThetaLeeNosal.theta_lee_nosal_of_RH hRH hx

end PseudoPrime.AnalyticNumberTheory.Arithmetic
