/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Endpoint bounds for signed numerators over square roots -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: any signed numerator and 0<lo<=x<=hi. Claim: division by sqrt(x)
is bounded by the maximum of the two endpoint quotients. Split the sign of
the numerator. Role: avoid replacing negative numerators by zero. -/
theorem signed_div_le_max_endpoints {a lo x hi : ℝ} (hlo : 0 < lo) (hlox : lo ≤ x) (hxhi : x ≤ hi) :
    a / Real.sqrt x ≤ max (a / Real.sqrt lo) (a / Real.sqrt hi) := by
  have hx := hlo.trans_le hlox
  have hhi := hx.trans_le hxhi
  by_cases ha : 0 ≤ a
  · apply le_trans ?_ (le_max_left _ _)
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hlo)).mpr
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlox) ha
  · apply le_trans ?_ (le_max_right _ _)
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_pos.mpr hhi)).mpr
    exact mul_le_mul_of_nonpos_left (Real.sqrt_le_sqrt hxhi) (le_of_not_ge ha)

end PseudoPrime.Analysis
