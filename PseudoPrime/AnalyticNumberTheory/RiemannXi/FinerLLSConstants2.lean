/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ParameterizedReciprocalLowerBound
public import PseudoPrime.Analysis.FinerLLSConstants

/-! # Refined Euler, zero-mass and reciprocal constants for LLS -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Claim: the Riemann zero mass is at most 0.0231.
Proof: insert the improved Euler bound and existing logarithm bounds into its closed formula.
Role: reduce the factorization-sensitive Part 1 correction. -/
theorem riemannZeroMass_le_231_div_10000 : riemannZeroMass ≤ (231 / 10000 : ℝ) := by
  have hlo := Analysis.log_pi_ge_2096_div_1831
  have hhi := Analysis.log_four_sub_log_pi_gt_twenty_four
  rw [Real.log_four_eq] at hhi
  rw [riemannZeroMass, abs_le, Real.log_mul (by norm_num only) Real.pi_ne_zero, Real.log_four_eq]
  constructor <;>
    nlinarith only [hlo, hhi, Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.one_half_lt_eulerMascheroniConstant, Analysis.eulerMascheroniConstant_le_28861_div_50000]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
