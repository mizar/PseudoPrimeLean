/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampCutoff

/-! # Monotonicity of the compact exponential ramp -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For ordered real inputs, the compact exponential ramp is antitone.
Compare the exponential branches and the nonnegative decreasing linear ramp factor.
This gives monotonicity of arithmetic sums as the scale grows. -/
theorem exponentialRampWeight_antitone : Antitone exponentialRampWeight := by
  intro u v huv
  have he := Real.exp_le_exp.mpr (neg_le_neg huv)
  by_cases hv : v ≤ 247 / 100
  · rw [exponentialRampWeight_eq_exp_of_le_left (huv.trans hv),
      exponentialRampWeight_eq_exp_of_le_left hv]
    exact he
  · by_cases hu : u ≤ 247 / 100
    · rw [exponentialRampWeight_eq_exp_of_le_left hu]
      exact (exponentialRampWeight_bounds v).2.trans he
    · by_cases hr : v ≤ 99 / 40
      · rw [exponentialRampWeight_eq_middle (le_of_not_ge hu) (huv.trans hr),
          exponentialRampWeight_eq_middle (le_of_not_ge hv) hr]
        exact
          div_le_div_of_nonneg_right
            (mul_le_mul he (sub_le_sub_left huv _) (sub_nonneg.mpr hr) (Real.exp_pos _).le)
            (by norm_num only)
      · rw [exponentialRampWeight_eq_zero (le_of_not_ge hr)]
        exact (exponentialRampWeight_bounds u).1

end PseudoPrime.Analysis
