/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Rational-power upper bounds from integer-power certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: x>0, l>=0, natural m and d>0, and 1<=l^d*x^m.
Claim: x^(-m/d)<=l. Proof: raise both nonnegative sides to d and cancel the exponent.
Role: validate rational-power error bounds by exact arithmetic at finite endpoints. -/
theorem rpow_neg_nat_div_le_of_power_bound {x l : ℝ} (hx : 0 < x) (hl : 0 ≤ l) (m d : ℕ)
    (hd : 0 < d) (hcheck : 1 ≤ l ^ d * x ^ m) : x ^ (-(m : ℝ) / (d : ℝ)) ≤ l := by
  have hdR : (d : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd).ne'
  have he : (x ^ (-(m : ℝ) / (d : ℝ))) ^ d = (x ^ m)⁻¹ := by
    rw [← Real.rpow_mul_natCast hx.le, div_mul_cancel₀ _ hdR, Real.rpow_neg hx.le,
      Real.rpow_natCast]
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg hx.le _) hl hd.ne').mp
  rw [he, ← one_div]
  exact (div_le_iff₀ (pow_pos hx m)).mpr hcheck

end PseudoPrime.Analysis
