/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 14 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower14 : List ℚ :=
  [6340118 / 1000000000000, 6329852 / 1000000000000, 6218695 / 1000000000000,
    6188932 / 1000000000000, 6149608 / 1000000000000, 6120382 / 1000000000000,
    6101023 / 1000000000000, 6091382 / 1000000000000, 6072173 / 1000000000000,
    6034051 / 1000000000000, 6005715 / 1000000000000, 5958969 / 1000000000000,
    5949691 / 1000000000000, 5903653 / 1000000000000, 5862714 / 1000000000000,
    5840170 / 1000000000000, 5795505 / 1000000000000, 5768972 / 1000000000000,
    5716499 / 1000000000000, 5707829 / 1000000000000, 5690554 / 1000000000000,
    5681949 / 1000000000000, 5639237 / 1000000000000, 5588672 / 1000000000000,
    5580317 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power14_check :
    quarterMomentPowerCheck ((centerRows250.drop 75).take 25) quarterMomentPower14 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
