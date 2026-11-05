/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusRoots

/-! # Rational residual certificates for Gaussian surplus prefixes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Constant term in the Gaussian residual bound for prefix mass P. -/
noncomputable def jointSurplusB0 (P : ℝ) : ℝ :=
  13 + 3 * (12871 / 1000 - 2 * P) +
    (7 / 2) * (2129 / 2000) * (10971611 / 5000000) / (20115621 / 25000000)

/-- Inverse-square-root coefficient in the Gaussian residual bound. -/
noncomputable def jointSurplusB1 : ℝ :=
  21 * (2129 / 2000) - (7 / 2) * (2129 / 2000) * (28794111 / 12500000) / (20115621 / 25000000)

/-- Inverse-radius coefficient after applying the root budget. -/
noncomputable def jointSurplusB2 (R : ℝ) : ℝ :=
  12 * (2129 / 2000) + 4 * (1839 / 1000) * (2129 / 2000) -
    (7 / 2) * (2129 / 2000) * R / (20115621 / 25000000)

/-- Positive quadratic coefficient after bounding both reciprocal tails. -/
noncomputable def jointSurplusH (rho R t : ℝ) : ℝ :=
  -jointSurplusB2 R - (1419 / 10) * t - (512 / 9) / rho

/-- The 35000-prefix constants satisfy the strict square-completion certificate. -/
theorem jointSurplus_cert35000 :
    (0 : ℝ) < jointSurplusH 130 30 (11 / 20) ∧
      jointSurplusB1 ^ 2 <
        4 * jointSurplusH 130 30 (11 / 20) * (30 - jointSurplusB0 (554117 / 100000)) ∧
      (1 : ℝ) ≤ 130 * (11 / 20 : ℝ) ^ 8 := by
  norm_num only [jointSurplusH, jointSurplusB0, jointSurplusB1, jointSurplusB2, and_self]

/-- The 50000-prefix constants satisfy the strict square-completion certificate. -/
theorem jointSurplus_cert50000 :
    (0 : ℝ) < jointSurplusH 155 29 (8 / 15) ∧
      jointSurplusB1 ^ 2 <
        4 * jointSurplusH 155 29 (8 / 15) * (29 - jointSurplusB0 (1129059 / 200000)) ∧
      (1 : ℝ) ≤ 155 * (8 / 15 : ℝ) ^ 8 := by
  norm_num only [jointSurplusH, jointSurplusB0, jointSurplusB1, jointSurplusB2, and_self]

end PseudoPrime.PrimeTestBounds.MillerRabin
