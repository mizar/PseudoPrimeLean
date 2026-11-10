/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Split
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block5Part0
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block5Part1
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block5Part2
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block5Part3

/-! # Integration of bounded Korselt factor block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The factor interval is empty by joining its independently checked parts. -/
theorem korselt23_block5 : korseltFastRange23 120 20 = [] := by
  change korseltFastRange23 120 (5 + (5 + (5 + 5))) = []
  rw [korselt23_range_split, korselt23_range_split, korselt23_range_split]
  norm_num only at ⊢
  rw [korselt23_block5_part0, korselt23_block5_part1, korselt23_block5_part2,
    korselt23_block5_part3]
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
