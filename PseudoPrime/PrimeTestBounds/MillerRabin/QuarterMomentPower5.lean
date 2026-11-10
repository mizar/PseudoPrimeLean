/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower5 : List ℚ :=
  [58219691 / 1000000000000, 56715824 / 1000000000000, 55987522 / 1000000000000,
    54575930 / 1000000000000, 53891787 / 1000000000000, 52891503 / 1000000000000,
    52402676 / 1000000000000, 50979597 / 1000000000000, 50671917 / 1000000000000,
    49766837 / 1000000000000, 48033953 / 1000000000000, 47204133 / 1000000000000,
    45872118 / 1000000000000, 45102098 / 1000000000000, 44352962 / 1000000000000,
    44107755 / 1000000000000, 43385262 / 1000000000000, 42223264 / 1000000000000,
    41550245 / 1000000000000, 40894568 / 1000000000000, 40679756 / 1000000000000,
    40046252 / 1000000000000, 39428700 / 1000000000000, 39025587 / 1000000000000,
    38826548 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power5_check :
    quarterMomentPowerCheck ((centerRows0.drop 110).take 25) quarterMomentPower5 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
