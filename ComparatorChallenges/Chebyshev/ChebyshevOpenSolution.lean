/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! Open comparator solutions for challenges on the Chebyshev ψ and θ functions.

The declarations include both conditional and unconditional statements.
-/

@[expose] public section

namespace ComparatorChallenges.Chebyshev

-- Temporarily suppress warnings for the unfinished comparator solutions.
set_option warn.sorry false

/-- Under the Riemann hypothesis, every real `x ≥ 2657` satisfies the Lee–Nosal bound
`|θ(x) - x| / √x ≤ log x * (log x - log (log x)) / (8π)`.
The proof of this bound is left open in the comparator solution.
See Lee and Nosal, https://arxiv.org/abs/2312.05628. -/
theorem theta_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 2657 ≤ x) :
    |Chebyshev.theta x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  sorry

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

/-- For every real `x` with `11 < x ≤ 10^19`, the Chebyshev ψ error is at most
`(47 / 50) * √x`. The proof of Büthe's unconditional finite-range bound remains open here.
See Büthe, *An analytic method for bounding ψ(x)*, https://arxiv.org/abs/1511.02032. -/
theorem psi_buthe_bound {x : ℝ} (hx : 11 < x) (hx' : x ≤ 10 ^ 19) :
    |Chebyshev.psi x - x| ≤ (47 / 50 : ℝ) * Real.sqrt x := by sorry

end ComparatorChallenges.Chebyshev
