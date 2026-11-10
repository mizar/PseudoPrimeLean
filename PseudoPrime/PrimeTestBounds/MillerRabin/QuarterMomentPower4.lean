/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower4 : List ℚ :=
  [98681398 / 1000000000000, 96890106 / 1000000000000, 96014280 / 1000000000000,
    94300928 / 1000000000000, 91822851 / 1000000000000, 91020376 / 1000000000000,
    88680395 / 1000000000000, 86437072 / 1000000000000, 84284953 / 1000000000000,
    82898360 / 1000000000000, 80887168 / 1000000000000, 78326911 / 1000000000000,
    77096009 / 1000000000000, 74726936 / 1000000000000, 71928640 / 1000000000000,
    71389492 / 1000000000000, 68790096 / 1000000000000, 68288744 / 1000000000000,
    66819937 / 1000000000000, 65869159 / 1000000000000, 64483824 / 1000000000000,
    62709366 / 1000000000000, 61851828 / 1000000000000, 61430215 / 1000000000000,
    60600936 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power4_check :
    quarterMomentPowerCheck ((centerRows0.drop 85).take 25) quarterMomentPower4 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
