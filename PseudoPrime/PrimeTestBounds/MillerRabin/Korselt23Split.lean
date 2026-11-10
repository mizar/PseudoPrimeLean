/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltRange23

/-! # Splitting bounded Korselt factor searches -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Adjacent factor ranges concatenate without repeating a finite search. -/
theorem korselt23_range_split (lo m n : ℕ) :
    korseltFastRange23 lo (m + n) = korseltFastRange23 lo m ++ korseltFastRange23 (lo + m) n := by
  unfold korseltFastRange23
  rw [← List.range'_append]
  simp only [one_mul, List.flatMap_append]

end PseudoPrime.PrimeTestBounds.MillerRabin
