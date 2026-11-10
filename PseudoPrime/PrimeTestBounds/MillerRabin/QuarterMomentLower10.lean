/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower10

/-! # Reflected moment lower endpoint block -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The block's rational lower endpoints are below the actual inverse powers.
The previously certified endpoint data are shifted down by one unit. -/
theorem quarter_moment_lower10_check :
    quarterMomentLowerCheck ((centerRows0.drop 235).take 15)
        (quarterMomentPower10.map (fun u ↦ u - 1 / 1000000000000)) =
      true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
