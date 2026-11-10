/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower3 : List ℚ :=
  [212634496 / 1000000000000, 194840088 / 1000000000000, 189443255 / 1000000000000,
    186835733 / 1000000000000, 181793205 / 1000000000000, 174635012 / 1000000000000,
    172350709 / 1000000000000, 170114796 / 1000000000000, 161627599 / 1000000000000,
    156668201 / 1000000000000, 155706114 / 1000000000000, 150130841 / 1000000000000,
    144874316 / 1000000000000, 143188626 / 1000000000000, 138319040 / 1000000000000,
    135220960 / 1000000000000, 133714170 / 1000000000000, 129354461 / 1000000000000,
    126575357 / 1000000000000, 117576728 / 1000000000000, 115196315 / 1000000000000,
    114035468 / 1000000000000, 111770287 / 1000000000000, 104393095 / 1000000000000,
    101471659 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power3_check :
    quarterMomentPowerCheck ((centerRows0.drop 60).take 25) quarterMomentPower3 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
