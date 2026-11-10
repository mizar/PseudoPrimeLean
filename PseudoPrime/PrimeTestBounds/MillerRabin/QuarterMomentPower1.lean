/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower1 : List ℚ :=
  [11373410234 / 1000000000000, 9540459901 / 1000000000000, 7054561422 / 1000000000000,
    6183790765 / 1000000000000, 5475770688 / 1000000000000, 4891152045 / 1000000000000,
    4401984650 / 1000000000000, 4186615089 / 1000000000000, 3328444165 / 1000000000000,
    2830098209 / 1000000000000, 2624942776 / 1000000000000, 2280790443 / 1000000000000,
    2135453867 / 1000000000000, 1886444906 / 1000000000000, 1592406060 / 1000000000000,
    1510702197 / 1000000000000, 1400346922 / 1000000000000, 1302572221 / 1000000000000,
    1188534545 / 1000000000000, 1137496008 / 1000000000000, 1004035795 / 1000000000000,
    965147456 / 1000000000000, 928659732 / 1000000000000, 831694424 / 1000000000000,
    725939888 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power1_check :
    quarterMomentPowerCheck ((centerRows0.drop 10).take 25) quarterMomentPower1 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
