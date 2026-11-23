/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaHighBridge
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseBand

/-! # Lower Lee–Nosal estimate for theta from eight billion onward -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Under RH, the normalized lower theta error satisfies the Lee–Nosal bound for every
real x at least eight billion. Join the closed phase band and the high range at 279 billion. -/
theorem theta_lower_eight_billion (hRH : RiemannHypothesis) {x : ℝ} (hx : 8000000000 ≤ x) :
    (x - Chebyshev.theta x) / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  rcases le_total x 279000000000 with h | h
  · exact theta_lower_phase_band hRH hx h
  · exact theta_lower_from_279_billion hRH h

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
