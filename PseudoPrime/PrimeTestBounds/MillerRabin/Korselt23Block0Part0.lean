/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltRange23

/-! # Independent bounded Korselt factor block 0, part 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The kernel checks this smaller factor interval independently.
/-- The reordered parameter search has no candidate in this interval. -/
theorem korselt23_block0_part0 : korseltFastRange23 59 1 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
