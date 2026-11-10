/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltRange23

/-! # Independent bounded Korselt factor block 0, part 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
-- Kernel reduction of this interval exceeds the default recursion depth.
-- The kernel checks this smaller factor interval independently.
/-- The reordered parameter search has no candidate in this interval. -/
theorem korselt23_block0_part1 : korseltFastRange23 60 5 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
