/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 17 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower17 : List ℚ :=
  [4352171 / 1000000000000, 4341072 / 1000000000000, 4270040 / 1000000000000,
    4221968 / 1000000000000, 4195642 / 1000000000000, 4174774 / 1000000000000,
    4164404 / 1000000000000, 4148926 / 1000000000000, 4143788 / 1000000000000,
    4128435 / 1000000000000, 4072930 / 1000000000000, 4043166 / 1000000000000,
    4038240 / 1000000000000, 3999181 / 1000000000000, 3979882 / 1000000000000,
    3970289 / 1000000000000, 3941737 / 1000000000000, 3908848 / 1000000000000,
    3885630 / 1000000000000, 3881013 / 1000000000000, 3871806 / 1000000000000,
    3853500 / 1000000000000, 3839862 / 1000000000000, 3826303 / 1000000000000,
    3817307 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power17_check :
    quarterMomentPowerCheck ((centerRows250.drop 150).take 25) quarterMomentPower17 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
