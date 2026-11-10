/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Split
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block0Part0
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block0Part1
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block0Part2

/-! # Integration of the first bounded Korselt factor block -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first factor interval is empty by joining its independent parts. -/
theorem korselt23_block0 : korseltFastRange23 59 11 = [] := by
  change korseltFastRange23 59 (1 + (5 + 5)) = []
  rw [korselt23_range_split, korselt23_range_split]
  norm_num only at ⊢
  rw [korselt23_block0_part0, korselt23_block0_part1, korselt23_block0_part2]
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
