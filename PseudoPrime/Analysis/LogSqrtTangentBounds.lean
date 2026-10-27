/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption

/-! # Logarithm-over-square-root estimates from a real anchor -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive c and a, suppose log(c)+2 log(a)+d ≤ b a and 2 ≤ b a.
Then (log(c x)+d)/sqrt(x) ≤ b for every x ≥ a².
Apply log(t/a) ≤ t/a-1 at t=sqrt(x); the slope condition controls every
larger t. The real parameters allow independent cutoff and error budgets.
This lemma replaces scale-specific logarithmic tail arguments. -/
theorem log_mul_add_div_sqrt_le_of_anchor {c a b d x : ℝ} (hc : 0 < c) (ha : 0 < a) (hx : a ^ 2 ≤ x)
    (hlog : Real.log c + 2 * Real.log a + d ≤ b * a) (hslope : 2 ≤ b * a) :
    (Real.log (c * x) + d) / Real.sqrt x ≤ b := by
  have hx0 : 0 < x := (sq_pos_of_pos ha).trans_le hx
  have ht0 := Real.sqrt_pos.mpr hx0
  have ht : a ≤ Real.sqrt x := (Real.le_sqrt ha.le hx0.le).mpr hx
  have htan := Real.log_le_sub_one_of_pos (div_pos ht0 ha)
  rw [Real.log_div ht0.ne' ha.ne'] at htan
  have hcancel : a * (Real.sqrt x / a) = Real.sqrt x := mul_div_cancel₀ _ ha.ne'
  have he := Real.log_sqrt hx0.le
  have hprod := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr ht)
  rw [Real.log_mul hc.ne' hx0.ne', div_le_iff₀ ht0]
  nlinarith only [htan, hcancel, he, hprod, hlog, ha]

end PseudoPrime.Analysis
