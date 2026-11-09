/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltSearch

/-! # Shared bounded Korselt classification interfaces -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An empty next factor range leaves the accumulated candidate list unchanged.
This connects separately checked blocks without repeating their evaluation. -/
theorem korselt_rows_add_empty (m n : ℕ) (h : korseltCandidateRange m n = []) :
    korseltCandidateRows (m + n) = korseltCandidateRows m := by
  have hsplit := korseltCandidateRows_split m n
  have hzero : korseltCandidateRange 0 m = korseltCandidateRows m := by
    simp only [korseltCandidateRange, korseltCandidateRows, List.range_eq_range']
  rw [hzero, h, List.append_nil] at hsplit
  exact hsplit

end PseudoPrime.PrimeTestBounds.MillerRabin
