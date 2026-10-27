/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TwoPoleResolventBounds

/-! # Resolvent domination on either side of real pole pairs -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For c>0 and c^2<=abs(a*b), bound the two-pole norm on the imaginary axis by
1/(c^2+t^2), with no sign restriction on a*b. Use the conjugate-product bound for
nonnegative product and the negative real part of the ordinary product otherwise.
This extends resolvent domination to vertical lines between two real poles. -/
theorem twoPoleFunction_norm_le_abs_resolvent {a b c t : ℝ} (hc : 0 < c) (hab : c ^ 2 ≤ |a * b|) :
    ‖twoPoleFunction a b (Complex.I * t)‖ ≤ 1 / (c ^ 2 + t ^ 2) := by
  by_cases hp : 0 ≤ a * b
  · rw [abs_of_nonneg hp] at hab
    exact twoPoleFunction_norm_le_resolvent hc hab
  · rw [abs_of_neg (lt_of_not_ge hp)] at hab
    have he : ((Complex.I * (t : ℂ) + a) * (Complex.I * t + b)).re = a * b - t ^ 2 := by
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_add,
        sub_zero]
      ring
    have hd := Complex.re_le_norm (-((Complex.I * (t : ℂ) + a) * (Complex.I * t + b)))
    rw [Complex.neg_re, he, norm_neg, norm_mul] at hd
    have hpos : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
    have hb : c ^ 2 + t ^ 2 ≤ ‖Complex.I * (t : ℂ) + a‖ * ‖Complex.I * t + b‖ := by
      linarith only [hd, hab]
    rw [twoPoleFunction, norm_div, norm_one, norm_mul]
    exact one_div_le_one_div_of_le hpos hb

end PseudoPrime.Analysis
