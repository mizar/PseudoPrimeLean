/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Split
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block4Part0Sub0
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt23Block4Part0Sub1

/-! # Integration of bounded Korselt factor block 4, part 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The interval is empty by joining its independent subintervals. -/
theorem korselt23_block4_part0 : korseltFastRange23 100 5 = [] := by
  change korseltFastRange23 100 (2 + 3) = []
  rw [korselt23_range_split]
  norm_num only at ⊢
  rw [korselt23_block4_part0_sub0, korselt23_block4_part0_sub1]
  rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
