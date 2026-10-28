/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalWeightedLowerBound
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.PreciseZeroMassBounds

/-! # Parameterized reciprocal remainder and its precise uniform bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive quadratic coefficient a, the expression a*u^2-2*b*u
is bounded below by -b^2/a for all real b,u. Complete a square explicitly.
This keeps the numerical loss parameterized in reciprocal remainder estimates. -/
theorem quadratic_remainder_lower {a b u : ℝ} (ha : 0 < a) :
    -(b ^ 2 / a) ≤ a * u ^ 2 - 2 * b * u := by
  have hid : a * u ^ 2 - 2 * b * u + b ^ 2 / a = a * (u - b / a) ^ 2 := by
    field_simp [ha.ne']
    ring
  have hn := mul_nonneg ha.le (sq_nonneg (u - b / a))
  linarith only [hid, hn]

end PseudoPrime.Analysis
