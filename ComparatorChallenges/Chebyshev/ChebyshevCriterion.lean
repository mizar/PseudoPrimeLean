/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! # Challenges on the Chebyshev ψ function

These challenges state bounds for the Chebyshev ψ function whose solutions are complete.
Each declaration specifies its assumptions and range.
-/

@[expose] public section

namespace ComparatorChallenges.Chebyshev

/-- Under the Riemann hypothesis, every real `x ≥ 101` satisfies the Lee–Nosal bound
`|ψ(x) - x| / √x ≤ log x * (log x - log (log x)) / (8π)`.
This is the challenge statement; the separate solution supplies its proof.
See Lee and Nosal, https://arxiv.org/abs/2312.05628. -/
theorem psi_lee_nosal_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 101 ≤ x) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) := by
  sorry

/-- For every real `x` from 1423 through 1000000, the normalized Chebyshev ψ error is at most
`4 / 5`. This unconditional finite-range bound is proved in the comparator solution. -/
theorem psi_error_le_four_fifths_million {x : ℝ} (hx : 1423 ≤ x) (hx' : x ≤ 1000000) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤ (4 / 5 : ℝ) := by sorry

end ComparatorChallenges.Chebyshev
