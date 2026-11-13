/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScale43

/-! # Scaling and normalization of a Chebyshev zero-budget estimate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A zero-split error estimate with nonnegative low- and high-zero budgets
can be bounded by linear expressions in the relative width `δ`. The width is
`x * δ` with `0 ≤ δ ≤ 1/2`; this preserves an arbitrary tail bound `C`. -/
theorem psi_error_budget_scaled {x h δ C A : ℝ} (hx : 0 < x) (hh : 0 < h) (hd : 0 ≤ δ)
    (hd2 : δ ≤ 1 / 2) (hw : h = x * δ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hb :
      |Chebyshev.psi x - x| ≤
        h / 2 + Real.log (2 * Real.pi) + Real.sqrt (x + h) * A +
          ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * C +
          1 / h) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) + Real.sqrt x * (1 + δ / 2) * A +
        (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h * C +
        1 / h := by
  have hp := scale_power_bounds hx hd hd2
  rw [← hw] at hp
  have hl := mul_le_mul_of_nonneg_right hp.1 hA
  have hp' := add_le_add hp.2 (le_refl (x ^ (3 / 2 : ℝ)))
  have hh' := div_le_div_of_nonneg_right hp' hh.le
  have ht := mul_le_mul_of_nonneg_right hh' hC
  linarith only [hb, hl, ht]

/-- Divide a scaled zero-budget estimate by `sqrt x`, for `x > 0` and width
`h = x * δ`. The conclusion keeps the tail budget `C` intact; the proof uses
`x^(3/2) = x * sqrt x` and explicit cancellation of nonzero factors. -/
theorem psi_error_budget_normalize {x h δ C A : ℝ} (hx : 0 < x) (hw : h = x * δ)
    (hb :
      |Chebyshev.psi x - x| ≤
        h / 2 + Real.log (2 * Real.pi) + Real.sqrt x * (1 + δ / 2) * A +
          (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h * C +
          1 / h) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x + (1 + δ / 2) * A +
        (2 * (1 + δ) / δ) * C +
        1 / (h * Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hxp : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have hr := Real.rpow_add hx (1 : ℝ) (1 / 2 : ℝ)
    convert hr using 1
    · norm_num only
    · rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hh := div_le_div_of_nonneg_right hb hs.le
  have heq :
    (h / 2 + Real.log (2 * Real.pi) + Real.sqrt x * (1 + δ / 2) * A +
          (x ^ (3 / 2 : ℝ) * (1 + 2 * δ) + x ^ (3 / 2 : ℝ)) / h * C +
          1 / h) /
        Real.sqrt x =
      h / (2 * Real.sqrt x) + Real.log (2 * Real.pi) / Real.sqrt x + (1 + δ / 2) * A +
        (2 * (1 + δ) / δ) * C +
        1 / (h * Real.sqrt x) := by
    have hc1 := mul_inv_cancel₀ hx.ne'
    have hc3 := mul_inv_cancel₀ hs.ne'
    rw [hxp, hw]
    simp only [div_eq_mul_inv, mul_inv_rev]
    linear_combination
      (2 * (1 + δ) * δ⁻¹ * C * (Real.sqrt x * (Real.sqrt x)⁻¹)) * hc1 +
        ((1 + δ / 2) * A + 2 * (1 + δ) * δ⁻¹ * C) * hc3
  rw [heq] at hh
  exact hh

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
