/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealLog
public import Mathlib.Tactic.Linarith

/-! # Finite linear budgets with retained exceptional contributions -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Given finite supports S,T, weights w with total at most L, and a>=0,
suppose each cost f outside T is at most a*w. Then the full cost is at most
a*L plus the positive excesses on T. Bound each term and extend only the
nonnegative excess sum. This retains small-prime savings in witness budgets. -/
theorem finite_sum_le_linear_budget_add_excess (S T : Finset ℕ) (f w : ℕ → ℝ) {a L : ℝ} (ha : 0 ≤ a)
    (hbudget : ∑ p ∈ S, w p ≤ L) (htail : ∀ p ∈ S, p ∉ T → f p ≤ a * w p) :
    ∑ p ∈ S, f p ≤ a * L + ∑ p ∈ T, max 0 (f p - a * w p) := by
  classical
  have hpoint : ∀ p ∈ S, f p ≤ a * w p + if p ∈ T then max 0 (f p - a * w p) else 0 := by
    intro p hp
    by_cases hT : p ∈ T
    · rw [ite_eq_left hT]
      linarith only [le_max_right (0 : ℝ) (f p - a * w p)]
    · rw [ite_eq_right hT, add_zero]
      exact htail p hp hT
  have hsum := Finset.sum_le_sum hpoint
  have hexcess :
    (∑ p ∈ S, if p ∈ T then max 0 (f p - a * w p) else 0) ≤ ∑ p ∈ T, max 0 (f p - a * w p) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp hnot
      exact le_max_left 0 _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  exact hsum.trans (add_le_add (mul_le_mul_of_nonneg_left hbudget ha) hexcess)

end PseudoPrime.Analysis
