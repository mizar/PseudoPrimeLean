/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Data0
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Data1
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # Independent weighted row certificate -/

@[expose] public section

-- Each 456-entry array is checked independently to limit reduction size.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked recurrence adds the prime weight 235. -/
theorem target028_fine53_step0 :
    weightedPrimeRowCheck 235 455 target028Fine53Row1 target028Fine53Row0 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
