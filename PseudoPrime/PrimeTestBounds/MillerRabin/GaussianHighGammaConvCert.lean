/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExp
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaRational

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExp
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaRational

/-! # Rational comparisons at the high Gaussian convolution endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rounded exponential upper bound at the K186 cutoff. -/
theorem k186_conv_exp_check :
    gammaConvExpUpper (1 / 4 * 65) 48 ≤
      (876424821944363628869906866980179791729517573831 : ℚ) / 10 ^ 55 := by
  decide +kernel

/-- The rounded exponential times the shifted moment is bounded by the
complete K186 transform at the first-pole rate. -/
theorem k186_conv_moment_check :
    ((876424821944363628869906866980179791729517573831 : ℚ) / 10 ^ 55) *
        highGammaShiftMoment .k186 65 (1 / 4) ≤
      highGammaRatTransform .k186 (1 / 4) := by
  decide +kernel

/-- The rounded exponential upper bound at the K196 cutoff. -/
theorem k196_conv_exp_check :
    gammaConvExpUpper (3 / 4 * 80) 48 ≤ (87565107626965203384887328008 : ℚ) / 10 ^ 55 := by
  decide +kernel

/-- The rounded exponential times the shifted moment is bounded by the
complete K196 transform at the first-pole rate. -/
theorem k196_conv_moment_check :
    ((87565107626965203384887328008 : ℚ) / 10 ^ 55) * highGammaShiftMoment .k196 80 (3 / 4) ≤
      highGammaRatTransform .k196 (3 / 4) := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
