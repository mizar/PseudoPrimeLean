/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPrimePowerCosts

/-! # Reciprocal tails at arbitrary geometric bases -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: p>1, a real coefficient and any finite length N.
Claim: the reciprocal tail equals C/(p^N*(p-1)). Proof: factor p^N and sum the geometric
series. Role: normalize the cost of a tail envelope after retaining a finite prefix. -/
theorem gamma_reciprocal_power_tail_sum {p C : ℝ} (hp : 1 < p) (N : ℕ) :
    (∑' k : ℕ, C * (p ^ (k + N + 1))⁻¹) = C / (p ^ N * (p - 1)) := by
  have ht (k : ℕ) : C * (p ^ (k + N + 1))⁻¹ = (p ^ N)⁻¹ * (C * (p ^ (k + 1))⁻¹) := by
    rw [Nat.add_right_comm k N 1, pow_add, mul_inv_rev]
    ring
  simp only [ht, tsum_mul_left]
  have hg := tsum_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)
  norm_num only [Real.rpow_neg_one] at hg
  rw [hg]
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hr : p⁻¹ / (1 - p⁻¹) = 1 / (p - 1) := by
    have he : 1 - p⁻¹ = p⁻¹ * (p - 1) := by rw [mul_sub, inv_mul_cancel₀ hp0, mul_one]
    rw [he, mul_comm p⁻¹ (p - 1)]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (p - 1) (inv_ne_zero hp0)
  rw [hr]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end PseudoPrime.Analysis
