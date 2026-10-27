/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FixedPointDensityBounds

/-! # Signed fixed-point exponential lower bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- An executable lower exponential envelope for signed rational input a/b.
Nonnegative numerators use the lower Taylor sum; negative numerators use the
reciprocal of the upper Taylor sum. The scale and term count are explicit. -/
def expFixedPointSignedLower (a : ℤ) (b scale n : ℕ) : ℕ :=
  if 0 ≤ a then expFixedPointLowerSum a.toNat b scale n
  else scale * scale / expFixedPointUpperSum (-a).toNat b scale n

/-- For positive scale and denominator and |a|/b/(n+1)<=1/2, the signed
fixed-point result is at most scale exp(a/b). Split on the sign and apply the
proved Taylor or reciprocal envelope. This handles tilted Gaussian node values. -/
theorem expFixedPointSignedLower_le (a : ℤ) (b scale n : ℕ) (hb : 0 < b) (hs : 0 < scale)
    (hsize : (|(a : ℝ)| / b) / (n + 1 : ℕ) ≤ 1 / 2) :
    (expFixedPointSignedLower a b scale n : ℝ) ≤ (scale : ℝ) * Real.exp ((a : ℝ) / b) := by
  by_cases ha : 0 ≤ a
  · have he : (a.toNat : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
    rw [expFixedPointSignedLower, ite_eq_left ha]
    simpa only [he] using expFixedPointLowerSum_le_exp a.toNat b scale n
  · have han : a ≤ 0 := (lt_of_not_ge ha).le
    have har : (a : ℝ) ≤ 0 := by exact_mod_cast han
    have he : ((-a).toNat : ℝ) = -(a : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (neg_nonneg.mpr han)
    have hz : ((-a).toNat : ℝ) / b / (n + 1 : ℕ) ≤ 1 / 2 := by
      simpa only [he, abs_of_nonpos har] using hsize
    have hu := expFixedPointUpperSum_ge_exp (-a).toNat b scale n hb hz
    have hr := fixedPoint_reciprocal_exp_lower hs hu
    rw [expFixedPointSignedLower, ite_eq_right ha]
    simpa only [he, neg_div, neg_neg] using hr

end PseudoPrime.Analysis
