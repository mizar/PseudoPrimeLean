/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedProfiles

/-! # Rational constants for the refined Gamma moments

Certify square-root and exponential allowances before normalizing the exact envelope masses.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Claim: the exponential at 347/100 exceeds 321/10.
Proof: use twenty-six positive Taylor terms and exact rational arithmetic.
Role: certify the logarithm in the compact zeroth moment. -/
theorem gammaRefined_exp_lower : (321 / 10 : ℝ) < Real.exp (347 / 100) := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 347 / 100) 26
  apply lt_of_lt_of_le ?_ hs
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ,
    Nat.factorial_zero]

/-- Claim: the square root of 257 is less than 161/10.
Proof: compare squares with the positive rational upper value.
Role: certify both compact-moment allowances. -/
theorem gammaRefined_sqrt_upper : Real.sqrt 257 < (161 / 10 : ℝ) := by
  nlinarith only [Real.sq_sqrt (by norm_num only : (0 : ℝ) ≤ 257), Real.sqrt_nonneg 257]

/-- Claim: arsinh sixteen is less than 347/100.
Proof: use its exponential formula, the square-root upper value and positive Taylor bound.
Role: certify the complete zeroth envelope mass. -/
theorem gammaRefined_arsinh_upper : Real.arsinh 16 < (347 / 100 : ℝ) := by
  apply Real.exp_lt_exp.mp
  rw [Real.exp_arsinh]
  norm_num only
  nlinarith only [gammaRefined_sqrt_upper, gammaRefined_exp_lower]

/-- Claim: the normalized zeroth envelope integral is at most three halves.
Proof: use its exact compact and tail mass, the arsinh allowance and pi greater than 3.14.
Role: replace the old zeroth Gamma moment constant sixteen fifths. -/
theorem gammaRefinedZeroEnvelope_normalized_le :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaRefinedEnvelope gammaRefinedCompactZero 1 t) ≤
      (3 / 2 : ℝ) := by
  rw [gammaRefinedZeroEnvelope_integral, one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos)]
  nlinarith only [gammaRefined_arsinh_upper, Real.pi_gt_d2]

/-- Claim: the normalized first envelope integral is at most one.
Proof: use its exact square-root mass and pi greater than three.
Role: replace the old first Gamma moment constant five thirds. -/
theorem gammaRefinedFirstEnvelope_normalized_le :
    (1 / (2 * Real.pi)) *
        (∫ t : ℝ, gammaRefinedEnvelope (fun u ↦ u * gammaRefinedCompactZero u) (31 / 16) t) ≤
      1 := by
  rw [gammaRefinedFirstEnvelope_integral, one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos)]
  nlinarith only [gammaRefined_sqrt_upper, Real.pi_gt_three]

end PseudoPrime.Analysis
