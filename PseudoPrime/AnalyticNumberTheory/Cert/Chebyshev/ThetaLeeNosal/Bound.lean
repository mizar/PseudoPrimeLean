/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.ThetaTransfer
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.Lower
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosal

/-! # The two-sided Lee–Nosal bound for theta -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Under RH, the normalized absolute theta error satisfies the Lee–Nosal bound for
every real x ≥ 2657. Combine the lower estimate with the psi upper bound via theta ≤ psi. -/
theorem theta_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 2657 ≤ x) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  have hs := Real.sqrt_pos.mpr ((by norm_num only : (0 : ℝ) < 2657).trans_le hx)
  have hp := Arithmetic.psi_lee_nosal_of_RH hRH ((by norm_num only : (101 : ℝ) ≤ 2657).trans hx)
  have hl := theta_lower_lee_nosal_of_RH hRH hx
  exact
    (div_le_iff₀ hs).2
      (Joint.theta_abs_of_lower le_rfl ((div_le_iff₀ hs).1 hp) ((div_le_iff₀ hs).1 hl))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
