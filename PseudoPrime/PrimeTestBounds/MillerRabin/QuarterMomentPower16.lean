/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 16 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower16 : List ℚ :=
  [4890640 / 1000000000000, 4850542 / 1000000000000, 4843911 / 1000000000000,
    4771938 / 1000000000000, 4752611 / 1000000000000, 4746198 / 1000000000000,
    4727041 / 1000000000000, 4714340 / 1000000000000, 4695393 / 1000000000000,
    4651662 / 1000000000000, 4633124 / 1000000000000, 4620832 / 1000000000000,
    4614706 / 1000000000000, 4596408 / 1000000000000, 4584274 / 1000000000000,
    4566172 / 1000000000000, 4560164 / 1000000000000, 4530316 / 1000000000000,
    4512559 / 1000000000000, 4494917 / 1000000000000, 4454186 / 1000000000000,
    4442659 / 1000000000000, 4425460 / 1000000000000, 4391386 / 1000000000000,
    4368907 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power16_check :
    quarterMomentPowerCheck ((centerRows250.drop 125).take 25) quarterMomentPower16 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
