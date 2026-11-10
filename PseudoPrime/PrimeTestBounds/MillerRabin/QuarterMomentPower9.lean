/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 9 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower9 : List ℚ :=
  [15585858 / 1000000000000, 15452835 / 1000000000000, 15278334 / 1000000000000,
    15149559 / 1000000000000, 15022548 / 1000000000000, 14571391 / 1000000000000,
    14531475 / 1000000000000, 14334550 / 1000000000000, 14180127 / 1000000000000,
    13990885 / 1000000000000, 13879310 / 1000000000000, 13769181 / 1000000000000,
    13624547 / 1000000000000, 13412198 / 1000000000000, 13342613 / 1000000000000,
    13239336 / 1000000000000, 13137358 / 1000000000000, 13103650 / 1000000000000,
    13003369 / 1000000000000, 12806527 / 1000000000000, 12646180 / 1000000000000,
    12365691 / 1000000000000, 12335153 / 1000000000000, 12274446 / 1000000000000,
    12184295 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power9_check :
    quarterMomentPowerCheck ((centerRows0.drop 210).take 25) quarterMomentPower9 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
