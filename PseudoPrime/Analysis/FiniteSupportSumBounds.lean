/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.PrimeWeightedExcessBounds

/-! # Finite sums with nonnegative supported terms -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A weighted finite sum supported in Q is at most the sum over Q when
all Q terms are nonnegative. Intersect the input set with Q and remove
the zero terms outside Q. This supplies the exact finite-support transfer
without assuming that every input prime itself lies below the cutoff. -/
theorem gamma_supported_sum_le_finite (R Q : Finset ℕ) (F : ℕ → ℝ)
    (hzero : ∀ p ∈ R, p ∉ Q → F p = 0) (hpos : ∀ p ∈ Q, 0 ≤ F p) :
    (∑ p ∈ R, F p) ≤ ∑ p ∈ Q, F p := by
  have he : (∑ p ∈ R ∩ Q, F p) = ∑ p ∈ R, F p :=
    Finset.sum_subset Finset.inter_subset_left
      (fun p hp hnot ↦ hzero p hp (fun hq ↦ hnot (Finset.mem_inter.mpr ⟨hp, hq⟩)))
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p hp hnot ↦ hpos p hp)

end PseudoPrime.Analysis
