/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 15 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower15 : List ℚ :=
  [5514200 / 1000000000000, 5506025 / 1000000000000, 5481620 / 1000000000000,
    5465447 / 1000000000000, 5457390 / 1000000000000, 5417395 / 1000000000000,
    5385742 / 1000000000000, 5315616 / 1000000000000, 5284927 / 1000000000000,
    5246970 / 1000000000000, 5224409 / 1000000000000, 5209456 / 1000000000000,
    5202006 / 1000000000000, 5187157 / 1000000000000, 5157667 / 1000000000000,
    5099502 / 1000000000000, 5092307 / 1000000000000, 5077966 / 1000000000000,
    5049481 / 1000000000000, 4993288 / 1000000000000, 4986336 / 1000000000000,
    4972479 / 1000000000000, 4944952 / 1000000000000, 4924470 / 1000000000000,
    4904126 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power15_check :
    quarterMomentPowerCheck ((centerRows250.drop 100).take 25) quarterMomentPower15 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
