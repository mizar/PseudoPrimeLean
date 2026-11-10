/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower6 : List ℚ :=
  [38239269 / 1000000000000, 37666357 / 1000000000000, 36742129 / 1000000000000,
    36561724 / 1000000000000, 36205224 / 1000000000000, 35681013 / 1000000000000,
    35169084 / 1000000000000, 35001101 / 1000000000000, 34020148 / 1000000000000,
    33703105 / 1000000000000, 33236501 / 1000000000000, 32630572 / 1000000000000,
    31898153 / 1000000000000, 31331339 / 1000000000000, 30645616 / 1000000000000,
    30114499 / 1000000000000, 29984065 / 1000000000000, 29725949 / 1000000000000,
    29345519 / 1000000000000, 29096294 / 1000000000000, 28608093 / 1000000000000,
    28250655 / 1000000000000, 28016395 / 1000000000000, 27557283 / 1000000000000,
    27332314 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power6_check :
    quarterMomentPowerCheck ((centerRows0.drop 135).take 25) quarterMomentPower6 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
