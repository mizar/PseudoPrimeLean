/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Numerical certificates for the index-six dual obstruction

The constants in this file are bounded by exact rational arithmetic and
global analytic inequalities. Both logarithm upper bounds use seven terms
of the nonnegative exponential series. The dual bound holds at every real
argument; it is not a finite sampling certificate.

The paper coefficient retains the epsilon beside `1/4`, as in Theorem 1.3.
The comparison with `60/121` therefore already holds at the strictly
positive epsilon `1/200`.
-/

@[expose] public section

namespace PseudoPrime.LLS.IndexSixBarrier

/-- The translation used by the index-six dual certificate. -/
noncomputable def shift : ℝ :=
  Real.log (5 / 2 : ℝ)

/-- The coefficient in the paper's Theorem 1.3 specialized to index six.
The epsilon is added before multiplying by the two index factors. -/
noncomputable def paperCoefficient (ε : ℝ) : ℝ :=
  (1 / 4 + ε) * (1 - 1 / 6) ^ 2 * (Real.log 12 / (Real.log 12 - 4)) ^ 2

/-- The bounded complex function used for the index-six dual certificate. -/
noncomputable def dualValue (u : ℝ) : ℂ :=
  2 * ((6 / 5 : ℂ) - (1 / 2 : ℂ) * Complex.exp (-Complex.I * (shift : ℂ) * (u : ℂ))) /
    (1 - Complex.I * (u : ℂ))

/-- The logarithmic translation is positive. -/
theorem log_five_halves_pos : 0 < Real.log (5 / 2 : ℝ) :=
  Real.log_pos (by norm_num only)

/-- The translation is strictly positive. -/
theorem shift_pos : 0 < shift :=
  log_five_halves_pos

/-- Seven positive Taylor terms give the strict rational upper bound
`log(5/2) < 11/12`. No decimal expansion is used. -/
theorem log_five_halves_lt_eleven_twelfths : Real.log (5 / 2 : ℝ) < 11 / 12 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 5 / 2)).mpr
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 11 / 12) 7
  have hr : (5 / 2 : ℝ) < ∑ i ∈ Finset.range 7, (11 / 12 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  exact hr.trans_le ht

/-- Seven positive Taylor terms also prove `log 12 < 5/2`. -/
theorem log_twelve_lt_five_halves : Real.log (12 : ℝ) < 5 / 2 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 12)).mpr
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 2) 7
  have hr : (12 : ℝ) < ∑ i ∈ Finset.range 7, (5 / 2 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  exact hr.trans_le ht

/-- The square of the translation has a simple rational upper bound. -/
theorem shift_sq_le : shift ^ 2 ≤ (121 / 144 : ℝ) := by
  have hs := mul_self_le_mul_self log_five_halves_pos.le log_five_halves_lt_eleven_twelfths.le
  calc
    shift ^ 2 ≤ (11 / 12 : ℝ) ^ 2 := by simpa only [shift, pow_two] using hs
    _ = 121 / 144 := by norm_num only

/-- At the positive epsilon `1/200`, the paper's index-six target is
strictly below the displayed rational comparison point. -/
theorem paperCoefficient_one_div_two_hundred_lt : paperCoefficient (1 / 200) < 425 / 864 := by
  have hl : 0 ≤ Real.log (12 : ℝ) := (Real.log_pos (by norm_num only : (1 : ℝ) < 12)).le
  have hd : 0 < 4 - Real.log (12 : ℝ) := by linarith only [log_twelve_lt_five_halves]
  have hr : Real.log (12 : ℝ) / (4 - Real.log 12) < 5 / 3 := by
    apply (div_lt_iff₀ hd).mpr
    linarith only [log_twelve_lt_five_halves]
  have hr0 : 0 ≤ Real.log (12 : ℝ) / (4 - Real.log 12) := div_nonneg hl hd.le
  have hs : (Real.log (12 : ℝ) / (4 - Real.log 12)) ^ 2 < (5 / 3 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_self_lt_mul_self hr0 hr
  have hneg : Real.log (12 : ℝ) / (Real.log 12 - 4) = -(Real.log 12 / (4 - Real.log 12)) := by
    rw [show Real.log (12 : ℝ) - 4 = -(4 - Real.log 12) by ring, div_neg]
  calc
    paperCoefficient (1 / 200) = (17 / 96 : ℝ) * (Real.log 12 / (4 - Real.log 12)) ^ 2 := by
      unfold paperCoefficient
      rw [hneg, neg_sq]
      norm_num only
    _ < (17 / 96 : ℝ) * (5 / 3) ^ 2 := mul_lt_mul_of_pos_left hs (by norm_num only)
    _ = 425 / 864 := by norm_num only

/-- The rational gap separating the paper target from the dual barrier. -/
theorem rational_gap : (425 / 864 : ℝ) < 60 / 121 := by norm_num only

/-- The index-six paper target at epsilon `1/200` is below `60/121`. -/
theorem paperCoefficient_one_div_two_hundred_lt_barrier : paperCoefficient (1 / 200) < 60 / 121 :=
  paperCoefficient_one_div_two_hundred_lt.trans rational_gap

/-- A real-variable form of the dual bound. The quadratic cosine bound
and `shift² ≤ 121/144` control the expression for every real `u`. -/
theorem dual_ratio_le (u : ℝ) :
    ((49 / 25 : ℝ) + (24 / 5) * (1 - Real.cos (shift * u))) / (1 + u ^ 2) ≤ 121 / 60 := by
  have hd : 0 < 1 + u ^ 2 := by linarith only [sq_nonneg u]
  apply (div_le_iff₀ hd).mpr
  have hc := Real.one_sub_sq_div_two_le_cos (x := shift * u)
  have hs := mul_le_mul_of_nonneg_right shift_sq_le (sq_nonneg u)
  nlinarith only [hc, hs]

/-- The exact squared norm of the complex dual function. This separates
the complex exponential identities from the real-variable estimate. -/
theorem dualValue_norm_sq_eq (u : ℝ) :
    ‖dualValue u‖ ^ 2 = ((49 / 25 : ℝ) + (24 / 5) * (1 - Real.cos (shift * u))) / (1 + u ^ 2) := by
  have hre : (Complex.exp (-Complex.I * (shift : ℂ) * (u : ℂ))).re = Real.cos (shift * u) := by
    simp only [neg_mul, Complex.exp_re, Complex.neg_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.mul_im, one_mul, zero_add, neg_zero, Real.exp_zero, Complex.neg_im, Real.cos_neg]
  have him : (Complex.exp (-Complex.I * (shift : ℂ) * (u : ℂ))).im = -Real.sin (shift * u) := by
    simp only [neg_mul, Complex.exp_im, Complex.neg_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.mul_im, one_mul, zero_add, neg_zero, Real.exp_zero, Complex.neg_im, Real.sin_neg,
      mul_neg]
  have hn :
    Complex.normSq
        (2 * ((6 / 5 : ℂ) - (1 / 2 : ℂ) * Complex.exp (-Complex.I * (shift : ℂ) * (u : ℂ)))) =
      (49 / 25 : ℝ) + (24 / 5) * (1 - Real.cos (shift * u)) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      hre, him]
    norm_num only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.one_re, Complex.one_im, zero_mul, mul_zero, zero_sub, sub_zero, add_zero, zero_add]
    nlinarith only [Real.cos_sq_add_sin_sq (shift * u)]
  have hd : Complex.normSq (1 - Complex.I * (u : ℂ)) = 1 + u ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, one_mul,
      Complex.sub_im, Complex.one_im, Complex.mul_im, zero_add, zero_sub, mul_neg, neg_mul, neg_neg,
      pow_two]
  rw [← Complex.normSq_eq_norm_sq, dualValue, Complex.normSq_div, hn, hd]

/-- The global dual certificate: the squared norm is at most `121/60`
at every real argument. -/
theorem dualValue_norm_sq_le (u : ℝ) : ‖dualValue u‖ ^ 2 ≤ (121 / 60 : ℝ) := by
  rw [dualValue_norm_sq_eq]
  exact dual_ratio_le u

end PseudoPrime.LLS.IndexSixBarrier
