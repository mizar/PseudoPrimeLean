/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComplexBlockSums

/-! # Complex interval sums over odd blocks -/

public section

namespace PseudoPrime.Analysis

/-- Certified intervals for positive odd indices through `N` enclose any block whose end is
within that bound. The proof uses each pointwise enclosure once and sums the interval endpoints.
This shared lemma lets independent finite-certificate blocks expose their sums without repeating
the oddness and index-bound proof for every endpoint. -/
theorem complex_odd_block_contains (G : ℤ) (B : ℕ → IntegerInterval × IntegerInterval) (f : ℕ → ℂ)
    (a m N : ℕ) (hN : 2 * (a + m) ≤ N + 1)
    (hf : ∀ n, Odd n → 0 < n → n ≤ N → complexIntervalContains (B n).1 (B n).2 G (f n)) :
    complexIntervalContains (intervalFinsetSum (Finset.range m) fun k ↦ (B (2 * (a + k) + 1)).1)
      (intervalFinsetSum (Finset.range m) fun k ↦ (B (2 * (a + k) + 1)).2) G
      (∑ k ∈ Finset.range m, f (2 * (a + k) + 1)) := by
  apply complex_sum_contains
  intro k hk
  have hk' : k < m := Finset.mem_range.mp hk
  apply hf
  · exact ⟨a + k, by simp only [two_mul]⟩
  · exact Nat.zero_lt_succ _
  · nlinarith only [hk', hN]

end PseudoPrime.Analysis
