/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Finite support for weighted positive excess -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For arbitrary real costs on natural bases, a finite set containing every
selected positive excess bounds its weighted sum. Terms outside the set vanish
and all remaining log-weighted positive parts are nonnegative. No primality
hypothesis is needed, so the reduction can be reused for different local models. -/
theorem prime_weighted_positive_excess_le_finite (F : ℕ → ℝ) (μ : ℝ) (R P : Finset ℕ)
    (htail : ∀ p ∈ R, p ∉ P → F p ≤ μ) :
    (∑ p ∈ R, Real.log p * max (F p - μ) 0) ≤ ∑ p ∈ P, Real.log p * max (F p - μ) 0 := by
  let G : ℕ → ℝ := fun p ↦ Real.log p * max (F p - μ) 0
  have he : (∑ p ∈ R ∩ P, G p) = ∑ p ∈ R, G p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have hpP : p ∉ P := fun h ↦ hnot (Finset.mem_inter.mpr ⟨hp, h⟩)
    dsimp only [G]
    rw [max_eq_right (sub_nonpos.mpr (htail p hp hpP)), mul_zero]
  change (∑ p ∈ R, G p) ≤ ∑ p ∈ P, G p
  rw [← he]
  exact
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun p hp hnot ↦ mul_nonneg (Real.log_natCast_nonneg p) (le_max_right _ _))

end PseudoPrime.Analysis
