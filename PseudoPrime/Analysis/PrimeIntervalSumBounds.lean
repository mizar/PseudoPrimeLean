/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedSummationByParts
public import Mathlib.Data.Rat.Cast.Order

/-! # Composition of upper bounds on adjacent prime intervals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Upper bounds for prime-filtered sums on adjacent natural intervals
add at fixed summand F. Rewrite the filtered sums as conditional full sums
and split the disjoint interval union. This composes certified support blocks. -/
theorem gamma_prime_interval_upper_add (F : ℕ → ℝ) {lo mid hi : ℕ} {a b : ℚ} (hl : lo ≤ mid)
    (hh : mid ≤ hi) (ha : (∑ p ∈ (Finset.Ioc lo mid).filter Nat.Prime, F p) ≤ (a : ℝ))
    (hb : (∑ p ∈ (Finset.Ioc mid hi).filter Nat.Prime, F p) ≤ (b : ℝ)) :
    (∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime, F p) ≤ ((a + b : ℚ) : ℝ) := by
  rw [Finset.sum_filter] at ha hb ⊢
  have hdis : Disjoint (Finset.Ioc lo mid) (Finset.Ioc mid hi) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hp).2) (Finset.mem_Ioc.mp hq).1
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hl hh, Finset.sum_union hdis, Rat.cast_add]
  exact add_le_add ha hb

end PseudoPrime.Analysis
