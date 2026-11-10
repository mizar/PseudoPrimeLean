/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower2 : List ℚ :=
  [681039387 / 1000000000000, 660263341 / 1000000000000, 621689642 / 1000000000000,
    603762498 / 1000000000000, 570342926 / 1000000000000, 511916485 / 1000000000000,
    486275266 / 1000000000000, 474231198 / 1000000000000, 468390684 / 1000000000000,
    451555726 / 1000000000000, 420708711 / 1000000000000, 411184387 / 1000000000000,
    368439086 / 1000000000000, 360758377 / 1000000000000, 339217735 / 1000000000000,
    319700699 / 1000000000000, 307686170 / 1000000000000, 301952763 / 1000000000000,
    290996093 / 1000000000000, 275735200 / 1000000000000, 270936710 / 1000000000000,
    248866982 / 1000000000000, 244804532 / 1000000000000, 236997281 / 1000000000000,
    233244891 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power2_check :
    quarterMomentPowerCheck ((centerRows0.drop 35).take 25) quarterMomentPower2 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
