/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCell92Principal
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaSecondCellBounds

/-! # Shared-scale power bound for Gamma gaps -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shared scale has negative `9/16` power at most `33/1250`.
An exact integer-power comparison certifies the analytic error bound used
throughout the grouped Gamma intervals. -/
theorem gammaFixed92_power_upper : (gammaMainCell92Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 33 / 1250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9
      16 (by decide)
  norm_num only [gammaMainCell92Scale, Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
