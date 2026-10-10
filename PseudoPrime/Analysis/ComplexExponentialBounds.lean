/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Cancellation bounds for complex exponentials and powers

Mean-value estimates in the closed left half-plane retain the vanishing factor at zero.
They give complex-power bounds uniform over shifts with nonnegative real part.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a complex number in the closed left half-plane, its exponential differs from one
by at most its norm. Apply the mean-value inequality along the real segment from zero to
the number; the exponential derivative has norm at most one. This retains cancellation
when a gamma shift approaches zero. -/
theorem norm_exp_sub_one_le_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) : ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  have hd (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.exp ((t : ℂ) * z)) (Complex.exp ((t : ℂ) * z) * z) t := by
    simpa only [id_eq, one_mul] using (((hasDerivAt_id (t : ℂ)).mul_const z).cexp).comp_ofReal
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖Complex.exp ((t : ℂ) * z) * z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg z)
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.1 hz)
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' (fun t _ ↦ (hd t).hasDerivWithinAt) hb
  simpa only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using h

/-- For a shift with nonnegative real part and a real cutoff greater than one,
the norm of the negative complex power minus one is at most the logarithm of the cutoff
times the shift norm. Express the power as an exponential and use the left-half-plane
mean-value bound. This supplies a uniform estimate near the repeated gamma pole. -/
theorem norm_cpow_neg_sub_one_le {κ : ℂ} (hκ : 0 ≤ κ.re) {x : ℝ} (hx : 1 < x) :
    ‖(x : ℂ) ^ (-κ) - 1‖ ≤ Real.log x * ‖κ‖ := by
  have hz : ((Real.log x : ℂ) * (-κ)).re ≤ 0 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.neg_re]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.log_pos hx).le (neg_nonpos.mpr hκ)
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hx).ne'), ←
    Complex.ofReal_log (zero_lt_one.trans hx).le]
  have hb := norm_exp_sub_one_le_of_re_nonpos hz
  simpa only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos hx)] using hb

end PseudoPrime.Analysis
