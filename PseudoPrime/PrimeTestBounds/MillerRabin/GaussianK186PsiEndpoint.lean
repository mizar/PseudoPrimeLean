/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation

/-! # Sharp profile endpoint for the finite K186 Chebyshev error -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing profile row gives the upper bound 84500 at five by one
integer Horner evaluation. -/
public theorem k186_profile_five_le_sharp : HighGaussianKernel.k186.realProfile.eval 5 ≤ 84500 := by
  have h := baseRow.eval_interval_contains 83 5 1 (by decide +kernel) (by decide)
  rw [base_row_poly, high_comp_profile_map] at h
  simp only [Analysis.IntegerInterval.Contains, Int.cast_ofNat, Int.cast_one, div_one] at h
  have hU : ((baseRow.evalInterval 83 5 1).upper : ℚ) / (baseRow.den : ℚ) ≤ 84500 := by
    decide +kernel
  exact
    h.2.trans
      (by
        simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] using
          (Rat.cast_le (K := ℝ)).mpr hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
