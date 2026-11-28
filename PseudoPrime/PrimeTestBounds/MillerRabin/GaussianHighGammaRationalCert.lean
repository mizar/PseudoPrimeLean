/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaRational
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell

/-! # Rational endpoint bounds for the high Gaussian gamma moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational lower-bound test at the K186 decaying cutoff passes. -/
theorem k186_gamma_endpoint_check :
    negativeEndpointExpUpper (9 / 4 * 65) * max 0 (highGammaShiftMoment .k186 65 (9 / 4)) ≤
      highGammaRatTransform .k186 (9 / 4) := by
  decide +kernel

/-- Rational exponential bound at the K196 endpoint. -/
private theorem k196_endpoint_exp_le :
    negativeEndpointExpUpper (11 / 4 * 80) ≤ (285256 : ℚ) / 10 ^ 101 := by decide +kernel

/-- Rational shifted moment bound at the K196 endpoint. -/
private theorem k196_endpoint_shift_le :
    highGammaShiftMoment .k196 80 (11 / 4) ≤ (3457 : ℚ) * 10 ^ 95 := by decide +kernel

/-- Rational complete transform bound at the K196 endpoint. -/
private theorem k196_endpoint_transform_ge :
    (18029 : ℚ) / 100 ≤ highGammaRatTransform .k196 (11 / 4) := by decide +kernel

/-- The rational K196 decay deficit bound at the cutoff 80. -/
theorem k196_gamma_endpoint_check :
    negativeEndpointExpUpper (11 / 4 * 80) * max 0 (highGammaShiftMoment .k196 80 (11 / 4)) -
        highGammaRatTransform .k196 (11 / 4) ≤
      806 := by
  have he := k196_endpoint_exp_le
  have hm := k196_endpoint_shift_le
  have ht := k196_endpoint_transform_ge
  have hM : max 0 (highGammaShiftMoment .k196 80 (11 / 4)) ≤ (3457 : ℚ) * 10 ^ 95 :=
    max_le (by norm_num only) hm
  have hmul := mul_le_mul he hM (le_max_left _ _) (by norm_num only : (0 : ℚ) ≤ 285256 / 10 ^ 101)
  exact (sub_le_sub hmul ht).trans (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
