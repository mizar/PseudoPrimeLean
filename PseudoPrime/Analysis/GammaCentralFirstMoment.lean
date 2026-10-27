/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaMellin

/-! # First absolute moments on positive Gamma vertical lines

One Gamma recurrence transfers the height factor to the next positive vertical line.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: any positive real part and any real height.
Claim: absolute height times the Gamma norm is bounded by the next vertical-line norm.
Proof: one recurrence and the imaginary-part lower bound on the complex argument norm.
Role: establish the first moment required by weighted digamma integration. -/
theorem abs_mul_norm_Gamma_vertical_le_shift {c : ℝ} (hc : 0 < c) (t : ℝ) :
    |t| * ‖Complex.Gamma ((c : ℂ) + Complex.I * t)‖ ≤
      ‖Complex.Gamma (((c + 1 : ℝ) : ℂ) + Complex.I * t)‖ := by
  let s : ℂ := (c : ℂ) + Complex.I * t
  have hr : s.re = c := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = t := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_mul, zero_add]
  have hn : s ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    rw [hr, Complex.zero_re] at he
    exact hc.ne' he
  have he : (((c + 1 : ℝ) : ℂ) + Complex.I * t) = s + 1 := by
    simp only [Complex.ofReal_add, Complex.ofReal_one, s]
    ring
  rw [he, Complex.Gamma_add_one s hn, norm_mul]
  have hb := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s) (norm_nonneg (Complex.Gamma s))
  rw [hi] at hb
  exact hb

/-- Input: any positive fixed real part.
Claim: the Gamma norm has an integrable absolute first height moment.
Proof: dominate it by the integrable norm on the next positive Gamma vertical line.
Role: discharge the first-moment condition for the actual Gamma Mellin kernel. -/
theorem integrable_abs_mul_norm_Gamma_vertical {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun t : ℝ ↦ |t| * ‖Complex.Gamma ((c : ℂ) + Complex.I * t)‖) := by
  have hcont : Continuous (fun t : ℝ ↦ |t| * ‖Complex.Gamma ((c : ℂ) + Complex.I * t)‖) :=
    continuous_abs.mul (continuous_Gamma_vertical hc).norm
  refine
    (integrable_Gamma_vertical (add_pos hc zero_lt_one)).norm.mono' hcont.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ (fun t ↦ ?_))
  rw [Real.norm_eq_abs,
    abs_of_nonneg
      (mul_nonneg (abs_nonneg t) (norm_nonneg (Complex.Gamma ((c : ℂ) + Complex.I * t))))]
  exact abs_mul_norm_Gamma_vertical_le_shift hc t

end PseudoPrime.Analysis
