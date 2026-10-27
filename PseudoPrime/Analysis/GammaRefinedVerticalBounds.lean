/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaVerticalNumericalBounds
public import Mathlib.Analysis.Convex.Jensen

/-! # Convexity-based Gamma envelopes for refined left moments

The real Gamma function is at most one between one and two.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a real argument in the closed interval from one to two.
Claim: its real Gamma value is at most one.
Proof: convexity bounds the value by the maximum of the two endpoint values.
Role: improve the recurrence numerators used in left-line moment envelopes. -/
theorem realGamma_le_one_of_one_le_of_le_two {r : ℝ} (hl : 1 ≤ r) (hu : r ≤ 2) :
    Real.Gamma r ≤ 1 := by
  have h :=
    Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num only [Set.mem_Ioi] : (1 : ℝ) ∈ Set.Ioi 0)
      (by norm_num only [Set.mem_Ioi] : (2 : ℝ) ∈ Set.Ioi 0) ⟨hl, hu⟩
  have h2 : Real.Gamma 2 = 1 := by
    have h := Real.Gamma_add_one (by norm_num only : (1 : ℝ) ≠ 0)
    norm_num only [Real.Gamma_one] at h
    exact h
  simpa only [Real.Gamma_one, h2, max_self] using h

/-- Input: real part minus one sixteenth and nonzero imaginary part.
Claim: the Gamma norm is at most the reciprocal square of the height.
Proof: two recurrences use a real Gamma numerator in the interval from one to two.
Role: the tail envelope for the refined zeroth left moment. -/
theorem norm_Gamma_neg_one_sixteenth_le_inv_sq {s : ℂ} (hs : s.re = -1 / 16) (hi : s.im ≠ 0) :
    ‖Complex.Gamma s‖ ≤ 1 / s.im ^ 2 := by
  have hb :=
    norm_Gamma_le_im_sq
      (by
        rw [hs]; norm_num only : -2 < s.re)
      hi
  have hn : Real.Gamma (s.re + 2) ≤ 1 :=
    realGamma_le_one_of_one_le_of_le_two
      (by
        rw [hs]; norm_num only)
      (by
        rw [hs]; norm_num only)
  exact hb.trans (div_le_div_of_nonneg_right hn (sq_nonneg s.im))

/-- Input: real part minus one sixteenth.
Claim: the Gamma norm is at most sixteen fifteenths divided by the argument norm.
Proof: one recurrence and convexity at the real shifted numerator.
Role: the compact-height envelope for both refined left moments. -/
theorem norm_Gamma_neg_one_sixteenth_le_inv_norm {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ ≤ (16 / 15 : ℝ) / ‖s‖ := by
  have hne : s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [hs, Complex.zero_re] at hr
    norm_num only at hr
  have hp : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re, hs]; norm_num only
  have hb := norm_Gamma_le_realGamma hp
  have hr : (s + 1).re = 15 / 16 := by
    rw [Complex.add_re, Complex.one_re, hs]; norm_num only
  rw [hr, Complex.Gamma_add_one s hne, norm_mul] at hb
  have hG : Real.Gamma (15 / 16) ≤ (16 / 15 : ℝ) := by
    have h := Real.Gamma_add_one (by norm_num only : (15 / 16 : ℝ) ≠ 0)
    have htop : Real.Gamma (15 / 16 + 1) ≤ 1 :=
      realGamma_le_one_of_one_le_of_le_two (by norm_num only) (by norm_num only)
    rw [h] at htop
    linarith only [htop]
  apply (le_div_iff₀ (norm_pos_iff.mpr hne)).mpr
  simpa only [mul_comm] using hb.trans hG

/-- Input: real part minus one sixteenth and nonzero height.
Claim: the Gamma norm times the cube of the absolute height is at most thirty-one sixteenths.
Proof: apply the inverse-square estimate after one shift and use Gamma convexity.
Role: integrable tail for the first refined Gamma moment. -/
theorem norm_Gamma_neg_one_sixteenth_mul_height_cubed_le {s : ℂ} (hs : s.re = -1 / 16)
    (hi : s.im ≠ 0) : ‖Complex.Gamma s‖ * |s.im| ^ 3 ≤ (31 / 16 : ℝ) := by
  have hne : s ≠ 0 := by
    intro h
    exact hi (congrArg Complex.im h)
  have hsi : (s + 1).im ≠ 0 := by simpa only [Complex.add_im, Complex.one_im, add_zero] using hi
  have hsr : -2 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re, hs]
    norm_num only
  have hb := norm_Gamma_le_im_sq hsr hsi
  have he : (s + 1).re + 2 = (47 / 16 : ℝ) := by
    rw [Complex.add_re, Complex.one_re, hs]
    norm_num only
  rw [he, Complex.add_im, Complex.one_im, add_zero] at hb
  have hg : Real.Gamma (47 / 16) ≤ (31 / 16 : ℝ) := by
    have hr := Real.Gamma_add_one (by norm_num only : (31 / 16 : ℝ) ≠ 0)
    norm_num only at hr
    rw [hr]
    exact
      (mul_le_mul_of_nonneg_left
            (realGamma_le_one_of_one_le_of_le_two (by norm_num only) (by norm_num only))
            (by norm_num only : (0 : ℝ) ≤ 31 / 16)).trans_eq
        (mul_one _)
  have hm :=
    mul_le_mul_of_nonneg_right (hb.trans (div_le_div_of_nonneg_right hg (sq_nonneg s.im)))
      (sq_nonneg s.im)
  rw [div_mul_cancel₀ _ (sq_pos_of_ne_zero hi).ne'] at hm
  rw [Complex.Gamma_add_one s hne, norm_mul] at hm
  have ha :=
    mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm s)
      (mul_nonneg (norm_nonneg (Complex.Gamma s)) (sq_nonneg s.im))
  have hid : ‖Complex.Gamma s‖ * |s.im| ^ 3 = |s.im| * (‖Complex.Gamma s‖ * s.im ^ 2) := by
    rw [pow_succ, sq_abs]
    ring
  rw [hid]
  exact ha.trans (by nlinarith only [hm])

/-- Input: real part minus one sixteenth and nonzero height.
Claim: the height-weighted Gamma norm is bounded by an inverse-square tail.
Proof: divide the certified cubic envelope by the positive squared height.
Role: directly integrable tail in the first-moment calculation. -/
theorem norm_Gamma_neg_one_sixteenth_mul_height_le_refined_tail {s : ℂ} (hs : s.re = -1 / 16)
    (hi : s.im ≠ 0) : ‖Complex.Gamma s‖ * |s.im| ≤ (31 / 16 : ℝ) / s.im ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_ne_zero hi)).mpr
  have he : (‖Complex.Gamma s‖ * |s.im|) * s.im ^ 2 = ‖Complex.Gamma s‖ * |s.im| ^ 3 := by
    rw [pow_succ |s.im| 2, sq_abs]
    ring
  rw [he]
  exact norm_Gamma_neg_one_sixteenth_mul_height_cubed_le hs hi

end PseudoPrime.Analysis
