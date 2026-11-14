/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalMellinWeightFast

/-! # Reusing coefficients of rational Mellin weights -/

public section

namespace PseudoPrime.Analysis

/-- A height-independent coefficient certificate can be reused for every
rational height in the transposed Gaussian weight. The hypothesis supplies
the exact coefficients on the finite index range; the conclusion replaces
their repeated computation by the supplied function. -/
theorem rational_gaussian_weight_coeffs (t a b p : ℚ) (n k : ℕ) (c : ℕ → ℚ)
    (hc :
      ∀ j ∈ Finset.range (n + 1),
        c j =
          ((a ^ j)⁻¹ *
            ∑ l ∈ Finset.Icc j n,
              ((l.factorial : ℚ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) * (l.choose j : ℚ) *
                (-p * ((k : ℚ) + 1) ^ 2) ^ (l - j))) :
    rationalGaussianWeightFast t a b p n k =
      rationalComplexScale 2
        (∑ j ∈ Finset.range (n + 1), rationalComplexScale (c j) (rationalMellinFalling t j)) := by
  unfold rationalGaussianWeightFast
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hc j hj]

end PseudoPrime.Analysis
