/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

/-! # Linear logarithm bounds from an arbitrary positive anchor -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive anchor a, suppose log a ≤ b a and 1 ≤ b a.
Then log L ≤ b L for all L ≥ a. Apply the logarithm tangent at L/a,
and use the slope condition beyond the anchor. The real parameters
allow the same lemma to verify logarithmic error budgets at other scales. -/
theorem log_le_mul_of_anchor {a b L : ℝ} (ha : 0 < a) (hL : a ≤ L) (hlog : Real.log a ≤ b * a)
    (hslope : 1 ≤ b * a) : Real.log L ≤ b * L := by
  have hL0 := ha.trans_le hL
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 ha)
  rw [Real.log_div hL0.ne' ha.ne'] at ht
  have hcancel : a * (L / a) = L := mul_div_cancel₀ _ ha.ne'
  have hprod := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hL)
  nlinarith only [ht, hcancel, hlog, hprod, ha]

end PseudoPrime.Analysis
