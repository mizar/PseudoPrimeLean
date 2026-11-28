/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPole

/-! # Exact rational evaluation of the high Gaussian gamma moments -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the complete normalized transform at a rational rate using
the compact numerator directly. -/
public def highGammaRatTransform (K : HighGaussianKernel) (s : ℚ) : ℚ :=
  K.normalization * (compactValue K s) ^ 2 / s ^ (2 * K.degree + 4)

/-- The rational evaluator computes the normalized square of the kernel polynomial. -/
public theorem high_gamma_rat_transform_eq (K : HighGaussianKernel) (s : ℚ) :
    highGammaRatTransform K s =
      K.normalization * (K.polynomial.eval₂ (RingHom.id ℚ) s) ^ 2 / s ^ (2 * K.degree + 4) := by
  rw [highGammaRatTransform, compact_value_eq]

/-- Compute the translated profile's signed Laplace moment at rational
shift and decay rate using the shared power coefficient row. -/
@[expose]
public def highGammaShiftMoment (K : HighGaussianKernel) (a s : ℚ) : ℚ :=
  let row := K.cellPowerRow a 1
  ∑ k ∈ Finset.range (2 * K.degree + 4), row[k]?.getD 0 * ((k.factorial : ℚ) / s ^ (k + 1))

end PseudoPrime.PrimeTestBounds.MillerRabin
