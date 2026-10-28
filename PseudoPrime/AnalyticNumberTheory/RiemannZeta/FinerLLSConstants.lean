/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ParameterizedReciprocalLowerBound
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2

/-! # Refined Euler, zero-mass and reciprocal constants for LLS -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Input: RH and a real cutoff at least two.
Claim: the reciprocal Mangoldt sum is at least log(x)-1.57755.
Proof: specialize the parameterized remainder with the refined Euler and zero-mass bounds.
Role: reduce the Part 2 correction without enumerating cutoffs. -/
theorem reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 2 ≤ x) :
    Real.log x - (31551 / 20000 : ℝ) ≤ Arithmetic.reciprocalWeightedMangoldtSum x := by
  have h :=
    reciprocalWeightedMangoldtSum_ge_of_parameters hRH hx
      Analysis.eulerMascheroniConstant_le_28861_div_50000 RiemannXi.riemannZeroMass_le_231_div_10000
      Analysis.log_two_mul_pi_gt.le (by norm_num only : (1 / 18 : ℝ) < 1837 / 1000)
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
