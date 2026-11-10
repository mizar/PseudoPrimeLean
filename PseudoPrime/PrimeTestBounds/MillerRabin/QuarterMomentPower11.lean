/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 11 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower11 : List ℚ :=
  [10585726 / 1000000000000, 10421645 / 1000000000000, 10375526 / 1000000000000,
    10352592 / 1000000000000, 10306971 / 1000000000000, 10239151 / 1000000000000,
    10149853 / 1000000000000, 10105679 / 1000000000000, 10083710 / 1000000000000,
    10018268 / 1000000000000, 9889447 / 1000000000000, 9784148 / 1000000000000,
    9763308 / 1000000000000, 9721845 / 1000000000000, 9701221 / 1000000000000,
    9660187 / 1000000000000, 9599165 / 1000000000000, 9478992 / 1000000000000,
    9361257 / 1000000000000, 9284087 / 1000000000000, 9170264 / 1000000000000,
    9114205 / 1000000000000, 9077142 / 1000000000000, 9022007 / 1000000000000,
    8949340 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power11_check :
    quarterMomentPowerCheck ((centerRows250.drop 0).take 25) quarterMomentPower11 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
