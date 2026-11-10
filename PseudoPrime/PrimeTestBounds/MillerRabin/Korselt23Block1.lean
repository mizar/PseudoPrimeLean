/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltRange23

/-! # Independent bounded Korselt factor block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 32768 in
-- Kernel reduction of this interval exceeds the default recursion depth.
-- The kernel checks this factor interval independently of the other blocks.
/-- The reordered parameter search has no candidate in this factor interval. -/
theorem korselt23_block1 : korseltFastRange23 70 10 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
