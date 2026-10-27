/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSignedWindowTransport

/-! # Rational root enclosures for signed window allowances -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: positive lower denominator and any signed numerator. Claim:
the quotient lies below the maximum of the endpoint quotients. Split the
numerator sign. Role: use rational denominator bounds without losing signs. -/
theorem gamma_div_le_max_of_interval {v a y b : ℝ} (ha : 0 < a) (hay : a ≤ y) (hyb : y ≤ b) :
    v / y ≤ max (v / a) (v / b) := by
  have hy := ha.trans_le hay
  have hb := hy.trans_le hyb
  by_cases hv : 0 ≤ v
  · apply le_trans ?_ (le_max_left _ _)
    exact (div_le_div_iff₀ hy ha).mpr (mul_le_mul_of_nonneg_left hay hv)
  · apply le_trans ?_ (le_max_right _ _)
    exact (div_le_div_iff₀ hy hb).mpr (mul_le_mul_of_nonpos_left hyb (le_of_not_ge hv))

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: rational-compatible root bounds on an ordered window.
Claim: replacing the actual roots by those bounds enlarges the local excess
allowance. Apply the signed quotient comparison at both endpoints.
Role: verify interval sums using exact rational arithmetic. -/
theorem gamma_window_excess_le_root_bounds {lo hi a b e N : ℝ} (ha : 0 < a) (hlohi : lo ≤ hi)
    (hlo : a ≤ Real.sqrt lo) (hhi : Real.sqrt hi ≤ b) :
    gammaRamifiedWindowExcessBound lo hi e N ≤ max (e + max (N / a) (N / b)) 0 := by
  have hl := gamma_div_le_max_of_interval (v := N) ha hlo ((Real.sqrt_le_sqrt hlohi).trans hhi)
  have hh := gamma_div_le_max_of_interval (v := N) ha (hlo.trans (Real.sqrt_le_sqrt hlohi)) hhi
  exact max_le_max (add_le_add le_rfl (max_le hl hh)) le_rfl

end PseudoPrime.Analysis
