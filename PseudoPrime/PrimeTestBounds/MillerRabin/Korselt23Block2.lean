/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltRange23

/-! # Independent bounded Korselt factor block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The kernel checks this factor interval independently of the other blocks.
/-- The reordered parameter search has no candidate in this factor interval. -/
theorem korselt23_block2 : korseltFastRange23 80 10 = [] := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
