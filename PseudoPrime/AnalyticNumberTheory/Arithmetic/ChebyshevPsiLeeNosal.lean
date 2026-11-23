/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH

/-! # The Lee–Nosal bound for the Chebyshev psi function -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH, the normalized Chebyshev ψ error satisfies the Lee–Nosal logarithmic bound
for every `x ≥ 101`. The low-zero signs and height-100 count bound are proved internally. -/
theorem psi_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  exact RiemannZeta.psi_lee_nosal_of_signs_RH hRH RiemannZeta.low_zero_100_sign_changes hx

end PseudoPrime.AnalyticNumberTheory.Arithmetic
