/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerPrefix

/-! # Extending the certified Euler prefix to larger cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 4096 in
-- Elaboration traverses the existing finite prime-power index set.
/-- At every cutoff at least 1000, the existing certified prime-power table
gives the same Euler lower bound. The omitted summands are nonnegative. -/
theorem refined_euler_prefix_1000_at {X : ℝ} (hX : 1000 ≤ X) :
    (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsub : refinedEulerPrefixSet ⊆ Finset.Ioc 0 ⌊X⌋₊ := by
    intro n hn
    have hp := quarter_euler_indices_pos n hn
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr (refinedEulerPrefixSet_le n hn)).trans hX
    exact Finset.mem_Ioc.mpr ⟨hp, Nat.le_floor hnX⟩
  have hn :
    ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      n ∉ refinedEulerPrefixSet →
        0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n _ _
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact refined_euler_prefix_1000_lower.le.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hn)

end PseudoPrime.PrimeTestBounds.MillerRabin
