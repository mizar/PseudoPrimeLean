/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 7 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower7 : List ℚ :=
  [26568065 / 1000000000000, 26043291 / 1000000000000, 25435562 / 1000000000000,
    25336526 / 1000000000000, 24850654 / 1000000000000, 24755304 / 1000000000000,
    24566388 / 1000000000000, 24472811 / 1000000000000, 24013536 / 1000000000000,
    23923369 / 1000000000000, 23393787 / 1000000000000, 23221502 / 1000000000000,
    23136135 / 1000000000000, 22966930 / 1000000000000, 22390338 / 1000000000000,
    22229929 / 1000000000000, 22150427 / 1000000000000, 21992808 / 1000000000000,
    21231491 / 1000000000000, 21084387 / 1000000000000, 20795123 / 1000000000000,
    20442555 / 1000000000000, 20167472 / 1000000000000, 20032189 / 1000000000000,
    19832024 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power7_check :
    quarterMomentPowerCheck ((centerRows0.drop 160).take 25) quarterMomentPower7 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
