/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-! # Finite quadratic-exponential moments and a uniform upper bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For any real coefficients, the displayed quadratic-exponential primitive
has derivative (a+bu+cu^2)exp(-u). Apply the polynomial product rule.
This is the exact finite-interval moment certificate. -/
theorem hasDerivAt_exponential_quadratic_primitive (a b c u : ℝ) :
    HasDerivAt (fun t : ℝ ↦ -(a + b * (t + 1) + c * (t ^ 2 + 2 * t + 2)) * Real.exp (-t))
      ((a + b * u + c * u ^ 2) * Real.exp (-u)) u := by
  have hp :=
    ((hasDerivAt_const u a).add (((hasDerivAt_id u).add_const 1).const_mul b)).add
      (((((hasDerivAt_id u).pow 2).add ((hasDerivAt_id u).const_mul 2)).add_const 2).const_mul c)
  have he := (hasDerivAt_id u).neg.exp
  have h := hp.neg.mul he
  apply h.congr_deriv
  change
    -(0 + b * 1 + c * (2 * u ^ (2 - 1 : ℕ) * 1 + 2 * 1)) * Real.exp (-u) +
        -(a + b * (u + 1) + c * (u ^ 2 + 2 * u + 2)) * (Real.exp (-u) * (-1)) =
      _
  norm_num only [pow_one]
  ring

/-- Integrate the quadratic-exponential density on [0,y] exactly.
Evaluate its explicit primitive at both endpoints. The result retains the
exponentially decaying endpoint term needed for the full-sum limit. -/
theorem integral_exponential_quadratic (a b c y : ℝ) :
    (∫ u in (0 : ℝ)..y, (a + b * u + c * u ^ 2) * Real.exp (-u)) =
      a + b + 2 * c - (a + b * (y + 1) + c * (y ^ 2 + 2 * y + 2)) * Real.exp (-y) := by
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ ↦ hasDerivAt_exponential_quadratic_primitive a b c u)
      ((show Continuous (fun u : ℝ ↦ (a + b * u + c * u ^ 2) * Real.exp (-u)) from
            (continuous_const.add (continuous_const.mul continuous_id) |>.add
                  (continuous_const.mul (continuous_id.pow 2))).mul
              (Real.continuous_exp.comp continuous_id.neg)).intervalIntegrable
        (0 : ℝ) y)
  simp only [zero_add, add_zero, mul_zero, zero_pow (by norm_num only : (2 : ℕ) ≠ 0), neg_zero,
    Real.exp_zero, mul_one] at h
  exact h.trans (by ring)

/-- For nonnegative coefficients and y>=0, the finite quadratic-exponential
integral is at most a+b+2c. The retained endpoint polynomial is nonnegative.
This bounds the logarithmically weighted error uniformly in the cutoff. -/
theorem integral_exponential_quadratic_le {a b c y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hy : 0 ≤ y) :
    (∫ u in (0 : ℝ)..y, (a + b * u + c * u ^ 2) * Real.exp (-u)) ≤ a + b + 2 * c := by
  rw [integral_exponential_quadratic]
  have hp : 0 ≤ a + b * (y + 1) + c * (y ^ 2 + 2 * y + 2) := by
    nlinarith only [ha, hb, hc, hy, mul_nonneg hb hy, mul_nonneg hc (sq_nonneg y), mul_nonneg hc hy]
  have he := mul_nonneg hp (Real.exp_pos (-y)).le
  linarith only [he]

end PseudoPrime.Analysis
