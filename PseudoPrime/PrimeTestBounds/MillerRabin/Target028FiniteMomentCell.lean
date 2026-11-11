/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FinitePairMoments

/-! # Uniform-triple finite-cell interface -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The explicit upper budget for a finite uniform-triple cell. It combines
the conductor, Gamma, reflected Euler and zero-mass terms with the upper bound
for the full principal sum; the cell's finite principal sum is compared to it. -/
noncomputable def target028MomentBudget (X U : ℝ) : ℝ :=
  (2 * U) *
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
            X ^ (-(27 / 25 : ℝ)) *
            ((21 / 8 : ℝ) + Real.log X) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        target028ReflectedMomentUpper X +
        (3 / 8 : ℝ) * U -
      (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    Real.sqrt X * (refinedSixPoleKernel.function (1 / 2)).re +
    ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
      ((1839 / 1000 : ℝ) * (Real.log X + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
        Real.sqrt X)

end PseudoPrime.PrimeTestBounds.MillerRabin
