/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Monotonicity of geometric ratios on the unit interval -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For any positive natural exponent, r/(1-r^j) increases on [0,1).
Power monotonicity makes its positive denominator decrease. This common
comparison handles both positive-power and odd-power dyadic costs. -/
theorem gamma_geometric_ratio_monotone {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s < 1) {j : ℕ}
    (hj : 0 < j) : r / (1 - r ^ j) ≤ s / (1 - s ^ j) := by
  have hs0 : 0 ≤ s := hr.trans hrs
  have hd : 0 < 1 - s ^ j := sub_pos.mpr (pow_lt_one₀ hs0 hs hj.ne')
  have hds : 1 - s ^ j ≤ 1 - r ^ j := sub_le_sub_left (pow_le_pow_left₀ hr hrs j) 1
  exact div_le_div₀ hs0 hrs hd hds

end PseudoPrime.Analysis
