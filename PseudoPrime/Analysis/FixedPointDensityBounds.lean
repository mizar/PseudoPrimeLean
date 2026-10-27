/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialFixedPointUpperBounds

/-! # Outward rounding through exponential density factors -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If upper bounds scale exp(x), natural division scale²/upper bounds scale exp(-x)
from below, for positive scale. Multiply by the inverse exponential before rounding.
This supplies the negative-input branch of the fixed-point certificate. -/
theorem fixedPoint_reciprocal_exp_lower {scale upper : ℕ} {x : ℝ} (hs : 0 < scale)
    (hu : (scale : ℝ) * Real.exp x ≤ (upper : ℝ)) :
    ((scale * scale / upper : ℕ) : ℝ) ≤ (scale : ℝ) * Real.exp (-x) := by
  have hp : (0 : ℝ) < upper := (mul_pos (Nat.cast_pos.mpr hs) (Real.exp_pos x)).trans_le hu
  have hm :=
    mul_le_mul_of_nonneg_right hu (mul_nonneg (Nat.cast_nonneg scale) (Real.exp_pos (-x)).le)
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hr : (scale : ℝ) * scale / upper ≤ (scale : ℝ) * Real.exp (-x) := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [hm, he]
  have hn :=
    (Nat.cast_div_le (m := scale * scale) (n := upper) :
      ((scale * scale / upper : ℕ) : ℝ) ≤ (scale * scale : ℕ) / upper)
  simp only [Nat.cast_mul] at hn
  exact hn.trans hr

/-- For positive scale, nonnegative first real factor a, and natural lower bounds
A<=scale a and B<=scale b, natural division AB/scale remains a lower bound for
scale ab. This preserves outward rounding through products of density factors. -/
theorem fixedPoint_mul_lower {scale A B : ℕ} {a b : ℝ} (hs : 0 < scale) (ha : 0 ≤ a)
    (hA : (A : ℝ) ≤ (scale : ℝ) * a) (hB : (B : ℝ) ≤ (scale : ℝ) * b) :
    ((A * B / scale : ℕ) : ℝ) ≤ (scale : ℝ) * (a * b) := by
  have hm := mul_le_mul hA hB (Nat.cast_nonneg B) (mul_nonneg (Nat.cast_nonneg scale) ha)
  have hr : (A : ℝ) * B / scale ≤ (scale : ℝ) * (a * b) := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr hs)).mpr
    nlinarith only [hm]
  have hn :=
    (Nat.cast_div_le (m := A * B) (n := scale) : ((A * B / scale : ℕ) : ℝ) ≤ (A * B : ℕ) / scale)
  simp only [Nat.cast_mul] at hn
  exact hn.trans hr

/-- For nonnegative x and positive integer lower<=scale exp(x), the truncated
integer scale-ceil(scale²/lower) is at most scale(1-exp(-x)).
The reciprocal reverses the exponential inequality; clipping at zero preserves the bound.
This justifies the cutoff factor in each midpoint certificate. -/
theorem fixedPoint_cutoff_lower {scale lower : ℕ} {x : ℝ} (hx : 0 ≤ x) (hl : 0 < lower)
    (hb : (lower : ℝ) ≤ (scale : ℝ) * Real.exp x) :
    ((scale - ((scale * scale + lower - 1) / lower) : ℕ) : ℝ) ≤
      (scale : ℝ) * (1 - Real.exp (-x)) := by
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-x)).le
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hr : (scale : ℝ) * Real.exp (-x) ≤ (scale : ℝ) * scale / lower := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hl)).mpr
    nlinarith only [hm, he, (Nat.cast_nonneg scale : (0 : ℝ) ≤ scale)]
  have hc := div_le_cast_ceilDiv (scale * scale) lower hl
  simp only [Nat.cast_mul] at hc
  have hrec := hr.trans hc
  by_cases h : (scale * scale + lower - 1) / lower ≤ scale
  · rw [Nat.cast_sub h]
    nlinarith only [hrec]
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge h)), Nat.cast_zero]
    exact
      mul_nonneg (Nat.cast_nonneg scale)
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)))

/-- Multiplying a natural lower fixed-point value by nonnegative rational a/b
and rounding down preserves the scaled real lower bound. Natural division and
real multiplication give the inequality, including zero denominator under Lean's convention.
This supplies the rational cutoff parameter and Gaussian normalization steps. -/
theorem fixedPoint_rational_mul_lower {A a b scale : ℕ} {x : ℝ} (hA : (A : ℝ) ≤ (scale : ℝ) * x) :
    ((A * a / b : ℕ) : ℝ) ≤ (scale : ℝ) * ((a : ℝ) / b * x) := by
  have h :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA (Nat.cast_nonneg a))
      (Nat.cast_nonneg b)
  have hn := (Nat.cast_div_le (m := A * a) (n := b) : ((A * a / b : ℕ) : ℝ) ≤ (A * a : ℕ) / b)
  simp only [Nat.cast_mul] at hn
  have he : (scale : ℝ) * x * a / b = (scale : ℝ) * ((a : ℝ) / b * x) := by ring
  exact hn.trans (h.trans_eq he)

end PseudoPrime.Analysis
