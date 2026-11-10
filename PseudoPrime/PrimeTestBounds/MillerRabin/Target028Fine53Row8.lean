/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Data8
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Data9
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # Independent weighted row certificate -/

@[expose] public section

-- Each 456-entry array is checked independently to limit reduction size.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- This recurrence check reduces 456 entries.
/-- The checked recurrence adds the prime weight 115. -/
theorem target028_fine53_step8 :
    weightedPrimeRowCheck 115 455 target028Fine53Row9 target028Fine53Row8 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
