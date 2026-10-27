/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.BoundedPrimeExclusion

/-! # Character logarithmic differences on a common finite support -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For ordered real cutoffs, the character logarithmic difference is a finite
sum over the larger support with the cutoff-restricted difference as real weight.
Pad the smaller sum by zero and distribute subtraction. This identifies the
weight used by progression orthogonality with the arithmetic explicit formula. -/
theorem sum_log_difference_weight_mul_character {q : ℕ} (χ : DirichletCharacter ℂ q) {x y : ℝ}
    (hxy : x ≤ y) :
    (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        ((logWeightedMangoldtTerm y n - (if n ≤ ⌊x⌋₊ then logWeightedMangoldtTerm x n else 0) : ℝ) :
            ℂ) *
          χ n) =
      characterLogWeightedSum y χ - characterLogWeightedSum x χ := by
  rw [characterLogWeightedSum_eq_extended χ hxy, characterLogWeightedSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Complex.ofReal_sub, sub_mul, characterLogWeightedTerm]
  split_ifs <;> simp only [Complex.ofReal_zero, zero_mul]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
