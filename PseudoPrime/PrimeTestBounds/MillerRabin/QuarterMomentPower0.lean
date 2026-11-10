/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, first block -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for the first ten prime powers. -/
def quarterMomentPower0 : List ℚ :=
  [334481888697 / 1000000000000, 176257829410 / 1000000000000, 111878133866 / 1000000000000,
    78637082628 / 1000000000000, 46210971280 / 1000000000000, 37421209520 / 1000000000000,
    31066822429 / 1000000000000, 22625571478 / 1000000000000, 17376788028 / 1000000000000,
    12516716838 / 1000000000000]

/-- The upper power endpoints enclose the actual powers. -/
theorem quarter_moment_power0_check :
    quarterMomentPowerCheck (centerRows0.take 10) quarterMomentPower0 = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
