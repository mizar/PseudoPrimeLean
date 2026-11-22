/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComputedComplexIntervals

/-! # Composition of complex interval block sums -/

public section

namespace PseudoPrime.Analysis

/-- Enclosures for two adjacent finite sums give an enclosure for their combined sum.
The two blocks may be proved independently; their endpoint sums are combined exactly,
without evaluating either block's certificate again. -/
theorem complex_sum_adjacent (G : ℤ) (A B : IntegerInterval × IntegerInterval) (f : ℕ → ℂ)
    (a m n : ℕ) (hA : complexIntervalContains A.1 A.2 G (∑ k ∈ Finset.range m, f (a + k)))
    (hB : complexIntervalContains B.1 B.2 G (∑ k ∈ Finset.range n, f ((a + m) + k))) :
    complexIntervalContains (A.1.add B.1) (A.2.add B.2) G
      (∑ k ∈ Finset.range (m + n), f (a + k)) := by
  rw [Finset.sum_range_add]
  simpa only [Nat.add_assoc] using complex_add_contains hA hB

end PseudoPrime.Analysis
