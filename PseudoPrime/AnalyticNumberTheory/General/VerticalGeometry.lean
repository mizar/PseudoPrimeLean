import PseudoPrime.AnalyticNumberTheory.General.MellinWeights
import PseudoPrime.AnalyticNumberTheory.General.LogQuadraticEnvelope

/-! Kernel-independent estimates extracted from the contour applications. -/

namespace PseudoPrime.AnalyticNumberTheory.General

/--
Input/assumptions: `A : ℕ` with `2 ≤ A`, `t : ℝ`.
Conclusion: `1 + t² ≤ ‖s_A(t)‖ * ‖s_A(t) - 1‖`, where `s_A(t) := -A - 1/2 + t i`.
Content: `‖s_A(t)‖ = √((A + 1/2)² + t²)` and `‖s_A(t) - 1‖ = √((A + 3/2)² + t²)`
(`Complex.norm_eq_sqrt_sq_add_sq`); since `(A + 1/2)² ≥ 1` and `(A + 3/2)² ≥ 1`,
`Real.sqrt_le_sqrt` gives `√(1 + t²) ≤ ‖s_A(t)‖` and `√(1 + t²) ≤ ‖s_A(t) - 1‖`; multiplying and
using `Real.sq_sqrt` (`√(1+t²) * √(1+t²) = 1 + t²`) finishes.
Role: the left-vertical denominator lower bound, feeding the reciprocal kernel's pointwise bound.
-/
theorem one_add_sq_le_norm_mul_norm_leftVertical (A : ℕ) (hA : 2 ≤ A) (t : ℝ) :
    1 + t ^ 2 ≤
      ‖((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ *
        ‖(((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hsim : s.im = t := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_im, Complex.sub_im, Complex.neg_im,
      Complex.natCast_im, neg_zero, Complex.inv_im, Complex.im_ofNat, Complex.normSq_ofNat,
      zero_div, sub_self, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
  have hs1re : (s - 1).re = -(A : ℝ) - 3 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.sub_re, Complex.add_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re]
    ring
  have hs1im : (s - 1).im = t := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.sub_im, Complex.add_im, Complex.neg_im,
      Complex.natCast_im, neg_zero, Complex.inv_im, Complex.im_ofNat, Complex.normSq_ofNat,
      zero_div, sub_self, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im, sub_zero]
  have hs_eq : ‖s‖ = Real.sqrt ((-(A : ℝ) - 1 / 2) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hsre, hsim]
  have hs1_eq : ‖s - 1‖ = Real.sqrt ((-(A : ℝ) - 3 / 2) ^ 2 + t ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hs1re, hs1im]
  have hA1sq : (1 : ℝ) ≤ (-(A : ℝ) - 1 / 2) ^ 2 := by nlinarith [hA']
  have hA3sq : (1 : ℝ) ≤ (-(A : ℝ) - 3 / 2) ^ 2 := by nlinarith [hA']
  have h1 : Real.sqrt (1 + t ^ 2) ≤ ‖s‖ := by
    rw [hs_eq]; exact Real.sqrt_le_sqrt (by linarith [hA1sq])
  have h2 : Real.sqrt (1 + t ^ 2) ≤ ‖s - 1‖ := by
    rw [hs1_eq]; exact Real.sqrt_le_sqrt (by linarith [hA3sq])
  have h3 : Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) = 1 + t ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  calc
    (1 : ℝ) + t ^ 2 = Real.sqrt (1 + t ^ 2) * Real.sqrt (1 + t ^ 2) := h3.symm
    _ ≤ ‖s‖ * ‖s - 1‖ := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (norm_nonneg _)

/--
Input/assumptions: `x : ℝ` with `0 < x`, `A : ℕ`, `t : ℝ`.
Conclusion: `‖(x : ℂ) ^ (s_A(t) - 1)‖ = x ^ (-(A : ℝ) - 3/2)`.
Content: `Complex.norm_cpow_eq_rpow_re_of_pos` reduces the norm to `x ^ ((s_A(t) - 1).re)`, and
`(s_A(t) - 1).re = -A - 3/2`.
Role: the exact power-factor norm, feeding the reciprocal kernel's pointwise bound.
-/
theorem norm_cpow_leftVertical_sub_one {x : ℝ} (hx : 0 < x) (A : ℕ) (t : ℝ) :
    ‖(x : ℂ) ^ ((((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1)‖ =
      x ^ (-(A : ℝ) - 3 / 2) := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hs1re : (s - 1).re = -(A : ℝ) - 3 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.sub_re, Complex.add_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re]
    ring
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hs1re]

/-! ### Squared-norm and power estimates on the left-vertical line -/

/--
Input/assumptions: `A : ℕ` with `2 ≤ A`, `t : ℝ`.
Conclusion: `1 + t² ≤ ‖s_A(t)‖²`, where `s_A(t) := -A - 1/2 + t i`.
Content: `‖s_A(t)‖² = (A + 1/2)² + t²` (`Complex.sq_norm_eq_re_sq_add_im_sq` or direct expansion);
since `(A + 1/2)² ≥ 1` (from `A ≥ 2`), the bound follows.
Role: bounds the denominator of `x^s / s²` on the left-vertical line.
-/
theorem one_add_sq_le_normSq_leftVertical (A : ℕ) (hA : 2 ≤ A) (t : ℝ) :
    1 + t ^ 2 ≤ ‖((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hA' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have hsim : s.im = t := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_im, Complex.sub_im, Complex.neg_im,
      Complex.natCast_im, neg_zero, Complex.inv_im, Complex.im_ofNat, Complex.normSq_ofNat,
      zero_div, sub_self, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add]
  have hs_eq : ‖s‖ ^ 2 = (-(A : ℝ) - 1 / 2) ^ 2 + t ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hsre, hsim, Real.sq_sqrt (by positivity)]
  have hA1sq : (1 : ℝ) ≤ (-(A : ℝ) - 1 / 2) ^ 2 := by nlinarith [hA']
  rw [hs_eq]; linarith [hA1sq]

/--
Input/assumptions: `x > 0`, `A : ℕ`, `t : ℝ`.
Conclusion: `‖(x : ℂ) ^ s_A(t)‖ = x ^ (-A - 1/2)`.
Content: `Complex.norm_cpow_eq_rpow_re_of_pos` reduces the norm to `x ^ (s_A(t)).re`.
Role: evaluates the numerator norm of `x^s / s²` on the left-vertical line.
-/
theorem norm_cpow_leftVertical_log {x : ℝ} (hx : 0 < x) (A : ℕ) (t : ℝ) :
    ‖(x : ℂ) ^ (((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ (-(A : ℝ) - 1 / 2) := by
  set s : ℂ := ((-(A : ℝ) - 1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hsre : s.re = -(A : ℝ) - 1 / 2 := by
    simp only [hs_def, one_div, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_inv, Complex.ofReal_ofNat, Complex.add_re, Complex.sub_re, Complex.neg_re,
      Complex.natCast_re, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
      div_self_mul_self', Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hsre]

end PseudoPrime.AnalyticNumberTheory.General
