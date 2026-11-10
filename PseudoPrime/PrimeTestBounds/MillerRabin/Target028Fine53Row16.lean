/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Data16
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # Independent weighted row certificate -/

@[expose] public section

-- Each 456-entry array is checked independently to limit reduction size.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The base-row reduction checks 456 entries.
/-- The final row counts the empty product. -/
theorem target028_fine53_base : weightedPrimeBaseCheck 455 target028Fine53Row16 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
