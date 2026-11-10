/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 18 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower18 : List ℚ :=
  [3812823 / 1000000000000, 3803878 / 1000000000000, 3790526 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power18_check :
    quarterMomentPowerCheck ((centerRows250.drop 175).take 3) quarterMomentPower18 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
