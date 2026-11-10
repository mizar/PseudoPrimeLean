/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltRange23

/-! # Independent bounded Korselt factor block 4, part 0, subpart 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The kernel checks this smaller factor interval independently.
/-- The reordered parameter search has no candidate in this factor interval. -/
theorem korselt23_block4_part0_sub0 : korseltFastRange23 100 2 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
