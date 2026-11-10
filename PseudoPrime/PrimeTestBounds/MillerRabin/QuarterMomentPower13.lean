/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerRowBlock250

/-! # Moment power endpoints, block 13 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper power endpoints for this block of prime powers. -/
def quarterMomentPower13 : List ℚ :=
  [7536631 / 1000000000000, 7495914 / 1000000000000, 7455555 / 1000000000000,
    7336584 / 1000000000000, 7297614 / 1000000000000, 7271822 / 1000000000000,
    7258982 / 1000000000000, 7182711 / 1000000000000, 7120146 / 1000000000000,
    7046235 / 1000000000000, 6997654 / 1000000000000, 6902117 / 1000000000000,
    6890325 / 1000000000000, 6820257 / 1000000000000, 6785659 / 1000000000000,
    6762752 / 1000000000000, 6751346 / 1000000000000, 6728627 / 1000000000000,
    6717315 / 1000000000000, 6661216 / 1000000000000, 6594901 / 1000000000000,
    6562147 / 1000000000000, 6529657 / 1000000000000, 6433748 / 1000000000000,
    6423233 / 1000000000000]

/-- Every rational endpoint encloses its corresponding prime power. -/
theorem quarter_moment_power13_check :
    quarterMomentPowerCheck ((centerRows250.drop 50).take 25) quarterMomentPower13 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
