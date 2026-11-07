/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointSignedBounds

/-! # Signed fixed-point exponential conversions -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Divide a certified signed fixed-point exponential lower bound by its positive
scale. The explicit Taylor-size condition ensures the lower endpoint is sound. -/
theorem exp_fixed_signed_lower_div (a : ℤ) (b scale n : ℕ) (hb : 0 < b) (hs : 0 < scale)
    (hsize : (|(a : ℝ)| / b) / (n + 1 : ℕ) ≤ 1 / 2) :
    (expFixedPointSignedLower a b scale n : ℝ) / (scale : ℝ) ≤ Real.exp ((a : ℝ) / b) := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr hs)).2
  exact (expFixedPointSignedLower_le a b scale n hb hs hsize).trans_eq (mul_comm _ _)

/-- A positive fixed-point lower bound for `exp(-a/b)` gives a rational upper
bound for `exp(a/b)` by reciprocal comparison. The signed Taylor certificate
and positive lower endpoint make the division valid. -/
theorem exp_upper_of_signed_fixed_lower (a : ℤ) (b scale n : ℕ) (hb : 0 < b) (hs : 0 < scale)
    (hsize : (|(((-a : ℤ) : ℝ))| / b) / (n + 1 : ℕ) ≤ 1 / 2)
    (hl : 0 < expFixedPointSignedLower (-a) b scale n) :
    Real.exp ((a : ℝ) / b) ≤ (scale : ℝ) / (expFixedPointSignedLower (-a) b scale n : ℝ) := by
  have h := expFixedPointSignedLower_le (-a) b scale n hb hs hsize
  simp only [Int.cast_neg, neg_div, Real.exp_neg, ← div_eq_mul_inv] at h
  have hm := (le_div_iff₀ (Real.exp_pos _)).1 h
  exact (le_div_iff₀ (Nat.cast_pos.mpr hl)).2 (by nlinarith only [hm])

end PseudoPrime.Analysis
