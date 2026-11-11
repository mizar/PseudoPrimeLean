/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevBounds

/-! # Chebyshev upper bound for the quarter-bound principal sums -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A real weight bounded above by `c ≥ 0` on natural indices through
`floor X`, with `X ≥ 1`, gives a weighted Mangoldt sum at most `3cX`.
Termwise comparison and the Chebyshev estimate supply a finite-sum upper
bound for truncations in the high-index principal-cost calculation. -/
theorem quarter_mangoldt_weight_le {X c : ℝ} (hX : 1 ≤ X) (hc : 0 ≤ c) (w : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Icc 0 ⌊X⌋₊, w n ≤ c) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, w n * ArithmeticFunction.vonMangoldt n) ≤ c * (3 * X) := by
  calc
    _ ≤ c * ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
      rw [Finset.mul_sum]
      exact
        Finset.sum_le_sum
          (fun n hn ↦ mul_le_mul_of_nonneg_right (hw n hn) ArithmeticFunction.vonMangoldt_nonneg)
    _ = c * Chebyshev.psi X := by rw [Chebyshev.psi_eq_sum_Icc]
    _ ≤ c * (3 * X) :=
      mul_le_mul_of_nonneg_left
        (AnalyticNumberTheory.Arithmetic.psi_le_three (zero_le_one.trans hX)) hc

end PseudoPrime.PrimeTestBounds.MillerRabin
