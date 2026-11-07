/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaMainCellBlock1
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaScalarTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCenterBound

/-! # Fixed scalar inputs for the second middle Gamma cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The second finite-cell right endpoint, retained as a rational number.
It is an upper enclosure for the next prime-power switching point.
The cell comparison below is valid for every real parameter below it. -/
def gammaSecondRight : ℚ :=
  40290610982379 / 1000000000000

/-- Exact row aggregation gives Euler prefix lower cap 3.99032 through 479.
The checked root and logarithm intervals are inherited from the center rows.
This cap leaves a positive scalar margin with the coarse second-cell errors. -/
theorem gamma_second_euler_check :
    (49879 / 12500 : ℚ) ≤
      ((centerRowsBelow 479).map (fun r ↦ r.lo * Analysis.gammaFiniteEulerLower r.ratios)).sum := by
  decide +kernel

/-- The actual Euler prefix through 479 is at least 3.99032.
Transfer exact support and the rational row aggregation to the real sum. -/
theorem gamma_second_euler_lower :
    (49879 / 12500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 479, Analysis.gammaResolventMangoldtWeight n := by
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    centerRowsBelow_euler_lower (by norm_num only : 479 ≤ 50000) (49879 / 12500)
      gamma_second_euler_check

/-- The second fixed scale satisfies a rational upper bound 397/10000 for its
negative 9/16 power. Integer-power arithmetic certifies the endpoint and
the existing real-power transfer proves the actual analytic inequality. -/
theorem gamma_second_power_upper : (gammaMainCell1Scale : ℝ) ^ (-9 / 16 : ℝ) ≤ 397 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound
      (by norm_num only [gammaMainCell1Scale, Rat.cast_div, Rat.cast_ofNat]) (by norm_num only) 9 16
      (by decide)
  norm_num only [gammaMainCell1Scale, Rat.cast_div, Rat.cast_ofNat]

/-- Coarse fixed endpoints still give a strict positive second-cell margin.
All inputs are rational, including the square-root lower cap 17.63,
the principal upper cap 17.544153 and the retained finite-main lower cap. -/
theorem gamma_second_scalar_check :
    (17544153 / 1000000 : ℚ) + 2 * (11783423 / 25000000) * gammaSecondRight - 477 / 100 +
        (3093 / 250 - 4 * (49879 / 12500)) +
        ((7 / 3) * gammaSecondRight + 12) / (1763 / 100) +
        (105 / 2) * (397 / 10000) +
        3 / (gammaMainCell1Scale * (1763 / 100)) <
      4 * gammaMainCell1Lower := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
