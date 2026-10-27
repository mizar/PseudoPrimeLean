/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointExecution
public import PseudoPrime.Analysis.FixedPointDensityBounds

/-! # Outward fixed-point intervals for negative exponentials -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Given a positive natural lower bound for scale*exp(x), ceiling division
of scale squared bounds scale*exp(-x) above. Multiply by the inverse exponential and
use the certified natural ceiling. This rounds negative exponentials outward. -/
theorem fixedPoint_reciprocal_exp_upper {scale lower : ℕ} {x : ℝ} (hl : 0 < lower)
    (hb : (lower : ℝ) ≤ (scale : ℝ) * Real.exp x) :
    (scale : ℝ) * Real.exp (-x) ≤ (((scale * scale + lower - 1) / lower : ℕ) : ℝ) := by
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-x)).le
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hr : (scale : ℝ) * Real.exp (-x) ≤ (scale : ℝ) * scale / lower := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hl)).mpr
    nlinarith only [hm, he, (Nat.cast_nonneg scale : (0 : ℝ) ≤ scale)]
  have hc := div_le_cast_ceilDiv (scale * scale) lower hl
  simp only [Nat.cast_mul] at hc
  exact hr.trans hc

/-- Given positive scale, nonnegative second real factor and natural upper
bounds for both scaled factors, ceiling division of their product bounds the scaled
real product above. This propagates fixed-point upper intervals through multiplication. -/
theorem fixedPoint_mul_upper {scale A B : ℕ} {a b : ℝ} (hs : 0 < scale) (hB0 : 0 ≤ b)
    (hA : (scale : ℝ) * a ≤ A) (hB : (scale : ℝ) * b ≤ B) :
    (scale : ℝ) * (a * b) ≤ (((A * B + scale - 1) / scale : ℕ) : ℝ) := by
  have hm := mul_le_mul hA hB (mul_nonneg (Nat.cast_nonneg scale) hB0) (Nat.cast_nonneg A)
  have hr : (scale : ℝ) * (a * b) ≤ (A : ℝ) * B / scale := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hs)).mpr
    nlinarith only [hm]
  have hc := div_le_cast_ceilDiv (A * B) scale hs
  simp only [Nat.cast_mul] at hc
  exact hr.trans hc

/-- The outward natural lower envelope for scale*exp(-a/b).
Take the rounded reciprocal of the existing fast upper Taylor sum, with explicit scale
and term count. Its soundness requires the upper Taylor remainder condition. -/
def expNegFixedLower (a b scale n : ℕ) : ℕ :=
  scale * scale / expFixedPointUpperSumFast a b scale n

/-- The outward natural upper envelope for scale*exp(-a/b).
Take ceiling division of scale squared by the fast lower Taylor sum. Positive scale
and term count ensure the divisor is positive. -/
def expNegFixedUpper (a b scale n : ℕ) : ℕ :=
  let l := expFixedPointLowerSumFast a b scale n
  (scale * scale + l - 1) / l

/-- For positive denominator and scale, with the displayed Taylor size
condition, the executable negative-exponential lower value is sound. Reuse the upper
Taylor bound and reciprocal lower rounding. -/
theorem expNegFixedLower_le (a b scale n : ℕ) (hb : 0 < b) (hs : 0 < scale)
    (hsize : ((a : ℝ) / b) / (n + 1 : ℕ) ≤ 1 / 2) :
    (expNegFixedLower a b scale n : ℝ) ≤ (scale : ℝ) * Real.exp (-(a : ℝ) / b) := by
  rw [expNegFixedLower, expFixedPointUpperSumFast_eq]
  simpa only [neg_div] using
    fixedPoint_reciprocal_exp_lower hs (expFixedPointUpperSum_ge_exp a b scale n hb hsize)

/-- For positive scale and term count, the executable negative-exponential
upper value is sound. The lower Taylor sum contains the positive constant term;
apply reciprocal upper rounding. No upper restriction on a/b is needed. -/
theorem expNegFixedUpper_ge (a b scale n : ℕ) (hs : 0 < scale) (hn : 0 < n) :
    (scale : ℝ) * Real.exp (-(a : ℝ) / b) ≤ (expNegFixedUpper a b scale n : ℝ) := by
  have hl := hs.trans_le (scale_le_expFixedPointLowerSum a b scale n hn)
  rw [expNegFixedUpper, expFixedPointLowerSumFast_eq]
  simpa only [neg_div] using
    fixedPoint_reciprocal_exp_upper hl (expFixedPointLowerSum_le_exp a b scale n)

end PseudoPrime.Analysis
