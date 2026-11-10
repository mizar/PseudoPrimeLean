/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Data13
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Data14
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # Independent weighted row certificate -/

@[expose] public section

-- Each 456-entry array is checked independently to limit reduction size.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- This recurrence check reduces 456 entries.
/-- The checked recurrence adds the prime weight 185. -/
theorem target028_fine53_step13 :
    weightedPrimeRowCheck 185 455 target028Fine53Row14 target028Fine53Row13 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
