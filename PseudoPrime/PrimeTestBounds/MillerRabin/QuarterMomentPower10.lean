/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock0

/-! # Moment power endpoints, block 10 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower10 : List ℚ :=
  [12154485 / 1000000000000, 12065765 / 1000000000000, 12007204 / 1000000000000,
    11978097 / 1000000000000, 11920229 / 1000000000000, 11749334 / 1000000000000,
    11721240 / 1000000000000, 11637614 / 1000000000000, 11582404 / 1000000000000,
    11181606 / 1000000000000, 11104161 / 1000000000000, 11078541 / 1000000000000,
    11027589 / 1000000000000, 10926826 / 1000000000000, 10705527 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power10_check :
    quarterMomentPowerCheck ((centerRows0.drop 235).take 15) quarterMomentPower10 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
