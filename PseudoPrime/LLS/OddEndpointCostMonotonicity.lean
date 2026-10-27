/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointTwoCostWitness

/-! # Monotonicity in the two arithmetic costs of odd-prime endpoint separation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At x>=1, increasing either reciprocal cost or logarithmic defect cost
increases the two-cost endpoint limit. The scalar coefficients are nonnegative.
No positivity of Y or the costs is required because division is totalized.
This compares exact value-at-two branches with a shared nonzero-branch envelope. -/
theorem oddEndpointTwoCostLimit_mono_costs (q : ℕ) {x Y c₁ c₂ D₁ D₂ : ℝ} (hx : 1 ≤ x) (hc : c₁ ≤ c₂)
    (hD : D₁ ≤ D₂) : oddEndpointTwoCostLimit q x Y c₁ D₁ ≤ oddEndpointTwoCostLimit q x Y c₂ D₂ := by
  have hk : 0 ≤ 2 + (Real.log x + 2) / Real.sqrt x :=
    add_nonneg (by norm_num only)
      (div_nonneg (by linarith only [Real.log_nonneg hx]) (Real.sqrt_nonneg x))
  have hm :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc (sq_nonneg (1 - 1 / Real.sqrt Y))) hk
  have hd := div_le_div_of_nonneg_right hD (Real.sqrt_nonneg x)
  dsimp only [oddEndpointTwoCostLimit, oddEndpointCostLimit]
  simp only [sub_div]
  linarith only [hm, hd]

end PseudoPrime.LLS.PaperStatements
