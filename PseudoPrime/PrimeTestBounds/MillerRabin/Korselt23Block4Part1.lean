/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltRange23

/-! # Independent bounded Korselt factor block 4, part 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
-- The kernel checks this factor interval independently of the other blocks.
/-- The reordered parameter search has no candidate in this interval. -/
theorem korselt23_block4_part1 : korseltFastRange23 105 5 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
