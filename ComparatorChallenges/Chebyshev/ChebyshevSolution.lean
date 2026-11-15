/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiSign100RH
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Completed comparator solutions for challenges on the Chebyshev ψ function.

The declarations include both conditional and unconditional bounds.
-/

@[expose] public section

namespace ComparatorChallenges.Chebyshev

/-- Under the Riemann hypothesis, every real `x ≥ 101` satisfies the Lee–Nosal bound
`|ψ(x) - x| / √x ≤ log x * (log x - log (log x)) / (8π)`.
The library theorem proves the bound using internally certified zero estimates.
See Lee and Nosal, https://arxiv.org/abs/2312.05628. -/
theorem psi_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) :=
  PseudoPrime.AnalyticNumberTheory.RiemannZeta.psi_lee_nosal_of_RH hRH hx

/-- For every real `x` from 1423 through 1000000, the normalized Chebyshev ψ error is at most
`4 / 5`. Divide the existing unconditional square-root error bound by the positive square root. -/
theorem psi_error_le_four_fifths_million {x : ℝ} (hx : 1423 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (4 / 5 : ℝ) := by
  have hpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  exact
    (div_le_iff₀ (Real.sqrt_pos.2 hpos)).2
      (PseudoPrime.AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hx hx')

end ComparatorChallenges.Chebyshev
