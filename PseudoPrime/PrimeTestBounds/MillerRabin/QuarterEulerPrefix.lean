/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerDerivatives

/-! # Reusable certified Euler prefixes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing checked prime-power rows restricted to a natural cutoff. -/
def quarterEulerPrefix (B : ℕ) : Finset ℕ :=
  refinedEulerPrefixSet.filter (fun n ↦ n ≤ B)

-- Kernel reduction checks positivity of the existing finite prime-power index set.
set_option maxRecDepth 4096 in
/-- Every index in the certified prime-power table is positive. -/
theorem quarter_euler_indices_pos : ∀ n ∈ refinedEulerPrefixSet, 0 < n := by decide +kernel

set_option maxRecDepth 4096 in
-- Applying the row theorem traverses the existing finite prime-power table.
/-- Any cutoff below the scale retains a certified Euler prefix. Each row
reuses its existing logarithm and power check; nonnegative omitted terms allow
the rational sum to bound the full prefix below. -/
theorem quarter_euler_prefix_lower {X : ℝ} (B : ℕ) (hB : (B : ℝ) ≤ X) :
    ((∑ n ∈ quarterEulerPrefix B, refinedEulerAtomLower n (refinedEulerData n) : ℚ) : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have hsum :=
    refined_euler_prefix_sound (quarterEulerPrefix B) refinedEulerData
      (fun n hn ↦ refined_euler_prefix_check n (Finset.mem_filter.mp hn).1)
  have hsub : quarterEulerPrefix B ⊆ Finset.Ioc 0 ⌊X⌋₊ := by
    intro n hn
    have hp := quarter_euler_indices_pos n (Finset.mem_filter.mp hn).1
    have hle : (n : ℝ) ≤ X := (Nat.cast_le.mpr (Finset.mem_filter.mp hn).2).trans hB
    exact Finset.mem_Ioc.mpr ⟨hp, Nat.le_floor hle⟩
  have hnonneg :
    ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      n ∉ quarterEulerPrefix B →
        0 ≤ ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
    intro n hn hnot
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (refined_six_euler_weight_nonneg_all n)
  exact hsum.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg)

end PseudoPrime.PrimeTestBounds.MillerRabin
