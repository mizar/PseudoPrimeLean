/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentPower0

/-! # Reflected moment lower endpoints, first block -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first block of rational lower endpoints is below the actual inverse
powers. The upper endpoints are reused as data, with one unit removed. -/
theorem quarter_moment_lower0_check :
    quarterMomentLowerCheck (centerRows0.take 10)
        (quarterMomentPower0.map (fun u ↦ u - 1 / 1000000000000)) =
      true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
