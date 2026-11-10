/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 12 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower12 : List ℚ :=
  [8913364 / 1000000000000, 8842117 / 1000000000000, 8806841 / 1000000000000,
    8685169 / 1000000000000, 8650909 / 1000000000000, 8599930 / 1000000000000,
    8583047 / 1000000000000, 8549441 / 1000000000000, 8499434 / 1000000000000,
    8482871 / 1000000000000, 8433497 / 1000000000000, 8352243 / 1000000000000,
    8193519 / 1000000000000, 8146860 / 1000000000000, 8115995 / 1000000000000,
    8100634 / 1000000000000, 8009456 / 1000000000000, 7919943 / 1000000000000,
    7890467 / 1000000000000, 7875797 / 1000000000000, 7803107 / 1000000000000,
    7717315 / 1000000000000, 7703167 / 1000000000000, 7633053 / 1000000000000,
    7577710 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power12_check :
    quarterMomentPowerCheck ((centerRows250.drop 25).take 25) quarterMomentPower12 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
