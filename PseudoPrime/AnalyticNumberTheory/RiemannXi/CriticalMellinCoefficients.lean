/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.Analysis.RationalMellinCoefficients
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinTerm

/-! # Shared coefficients for critical-line Mellin certificates -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Exact coefficients of one rational Gaussian weight can be certified once
and reused for every height `t`. The coefficient hypothesis refers only to
the grid cell and Gaussian index, while the conclusion retains the falling
factorials that carry the height dependence. -/
theorem certificate_weight_coeffs (t a b : ℚ) (k : ℕ) (c : ℕ → ℚ)
    (hc :
      ∀ j ∈ Finset.range (Analysis.rationalGaussianOrder k + 1),
        c j =
          ((a ^ j)⁻¹ *
            ∑ l ∈ Finset.Icc j (Analysis.rationalGaussianOrder k),
              ((l.factorial : ℚ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) * (l.choose j : ℚ) *
                (-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℚ) *
                    ((k : ℚ) + 1) ^ 2) ^
                  (l - j))) :
    certificateWeight t a b k =
      Analysis.rationalComplexScale 2
        (∑ j ∈ Finset.range (Analysis.rationalGaussianOrder k + 1),
          Analysis.rationalComplexScale (c j) (Analysis.rationalMellinFalling t j)) := by
  exact Analysis.rational_gaussian_weight_coeffs t a b _ _ k c hc

end PseudoPrime.AnalyticNumberTheory.RiemannXi
