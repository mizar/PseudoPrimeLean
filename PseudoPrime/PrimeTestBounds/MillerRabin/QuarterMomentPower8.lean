/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 8 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower8 : List ℚ :=
  [19635105 / 1000000000000, 19377469 / 1000000000000, 19187844 / 1000000000000,
    19063104 / 1000000000000, 18878462 / 1000000000000, 18696721 / 1000000000000,
    18458807 / 1000000000000, 18283598 / 1000000000000, 17941220 / 1000000000000,
    17829415 / 1000000000000, 17663827 / 1000000000000, 17609188 / 1000000000000,
    17527746 / 1000000000000, 17340089 / 1000000000000, 17287075 / 1000000000000,
    17129609 / 1000000000000, 16872318 / 1000000000000, 16821616 / 1000000000000,
    16571801 / 1000000000000, 16522564 / 1000000000000, 16376279 / 1000000000000,
    15949877 / 1000000000000, 15857580 / 1000000000000, 15811758 / 1000000000000,
    15720760 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power8_check :
    quarterMomentPowerCheck ((centerRows0.drop 185).take 25) quarterMomentPower8 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
