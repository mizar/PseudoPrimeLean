/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Rat.Defs

/-! # List partition for principal Gamma upper certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Splitting a rational list at any index preserves its sum. The first
block and remaining tail concatenate to the original list. This identity
allows individually certified principal upper blocks to be combined. -/
theorem rational_list_chunk_sum (xs : List ℚ) (n : ℕ) :
    (xs.take n).sum + (xs.drop n).sum = xs.sum := by rw [← List.sum_append, List.take_append_drop]

end PseudoPrime.PrimeTestBounds.MillerRabin
