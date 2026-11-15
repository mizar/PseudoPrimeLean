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

/-! Comparator solutions for challenges on the Chebyshev ψ and θ functions.

The declarations include both conditional and unconditional statements.
-/

@[expose] public section

namespace ComparatorChallenges.Chebyshev

-- Temporarily suppress warnings for the unfinished comparator solutions.
set_option warn.sorry false

/-- Under the Riemann hypothesis, every real `x ≥ 101` satisfies the Lee–Nosal bound
`|ψ(x) - x| / √x ≤ log x * (log x - log (log x)) / (8π)`.
The library theorem proves the bound using internally certified zero estimates.
See Lee and Nosal, https://arxiv.org/abs/2312.05628. -/
theorem psi_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) :=
  PseudoPrime.AnalyticNumberTheory.RiemannZeta.psi_lee_nosal_of_RH hRH hx

/-- Under the Riemann hypothesis, every real `x ≥ 2657` satisfies the Lee–Nosal bound
`|θ(x) - x| / √x ≤ log x * (log x - log (log x)) / (8π)`.
The proof of this bound is left open in the comparator solution.
See Lee and Nosal, https://arxiv.org/abs/2312.05628. -/
theorem theta_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 2657 ≤ x) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  sorry

/-- For every real `x` from 1423 through 1000000, the normalized Chebyshev ψ error is at most
`4 / 5`. Divide the existing unconditional square-root error bound by the positive square root. -/
theorem psi_error_le_four_fifths_million {x : ℝ} (hx : 1423 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (4 / 5 : ℝ) := by
  have hpos : 0 < x := lt_of_lt_of_le (by norm_num only) hx
  exact
    (div_le_iff₀ (Real.sqrt_pos.2 hpos)).2
      (PseudoPrime.AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million hx hx')

/-- For every real `x` from 1423 through 36076580711678, the normalized Chebyshev ψ error
is at most `4 / 5`. This unconditional finite-range assertion remains open here. -/
theorem psi_error_le_four_fifths {x : ℝ} (hx : 1423 ≤ x) (hx' : x ≤ 36076580711678) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (4 / 5 : ℝ) := by sorry

/-- At `x = 1422.99`, the normalized Chebyshev ψ error is strictly greater than `4 / 5`.
The exact rational counterexample remains open here. -/
theorem psi_error_lower_counterexample :
    |Chebyshev.psi (142299 / 100) - 142299 / 100| / Real.sqrt (142299 / 100) > (4 / 5 : ℝ) := by
  sorry

/-- At `x = 36076580711678.75`, the normalized Chebyshev ψ error is strictly greater than
`4 / 5`. This upper-endpoint counterexample remains open here. -/
theorem psi_error_upper_counterexample :
    |Chebyshev.psi (144306322846715 / 4) - 144306322846715 / 4| / Real.sqrt (144306322846715 / 4) >
      (4 / 5 : ℝ) := by
  sorry

/-- On the closed interval from 17 to 36076729684088, the normalized Chebyshev ψ error
is at most `81 / 100`. This unconditional finite-range assertion remains open here. -/
theorem psi_error_le_eighty_one_percent {x : ℝ} (hx : 17 ≤ x) (hx' : x ≤ 36076729684088) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (81 / 100 : ℝ) := by sorry

/-- At `x = 16.99`, the normalized Chebyshev ψ error exceeds `81 / 100`.
This exact rational counterexample remains open here. -/
theorem psi_error_81_lower_counterexample :
    |Chebyshev.psi (1699 / 100) - 1699 / 100| / Real.sqrt (1699 / 100) > (81 / 100 : ℝ) := by sorry

/-- At `x = 36076729684088.75`, the normalized Chebyshev ψ error exceeds `81 / 100`.
This upper-endpoint counterexample remains open here. -/
theorem psi_error_81_upper_counterexample :
    |Chebyshev.psi (144306918736355 / 4) - 144306918736355 / 4| / Real.sqrt (144306918736355 / 4) >
      (81 / 100 : ℝ) := by
  sorry

end ComparatorChallenges.Chebyshev
