/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleKernelMass

/-! Uniform fourth-order estimates on the symmetric contour strip. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The open strip with real part strictly between -4/5 and 4/5.
It excludes the fourth-order pole -25/26 and is wide enough for a symmetric
Mellin allowance exceeding one quarter. This supplies the enlarged contour kernel. -/
def fourWideRegion : Set ℂ :=
  {z | -(4 / 5 : ℝ) < z.re ∧ z.re < 4 / 5}

/-- In the extended strip the fourth-order denominator stays uniformly away from zero,
and its squared norm controls one plus the squared norm of the argument.
Use the real-part gap 21/125 and the explicit imaginary coefficient 26/25.
These two bounds supply holomorphy and uniform quadratic decay on the enlarged region. -/
theorem fourWide_denominator_bounds {z : ℂ} (hz : z ∈ fourWideRegion) :
    (21 / 125 : ℝ) ^ 2 ≤ ‖1 + (26 / 25 : ℂ) * z‖ ^ 2 ∧
      1 + ‖z‖ ^ 2 ≤ 100 * ‖1 + (26 / 25 : ℂ) * z‖ ^ 2 := by
  have hre : (21 / 125 : ℝ) < 1 + (26 / 25 : ℝ) * z.re := by linarith only [hz.1]
  have hs : z.re ^ 2 ≤ 1 := by
    have hl : -1 < z.re := (by norm_num only : (-1 : ℝ) < -(4 / 5)).trans hz.1
    have hu : z.re < 1 := hz.2.trans (by norm_num only : (4 / 5 : ℝ) < 1)
    nlinarith only [mul_nonneg (le_of_lt (by linarith only [hl] : 0 < 1 + z.re))
        (le_of_lt (by linarith only [hu] : 0 < 1 - z.re))]
  have hn :
    ‖1 + (26 / 25 : ℂ) * z‖ ^ 2 = (1 + (26 / 25 : ℝ) * z.re) ^ 2 + ((26 / 25 : ℝ) * z.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re,
      Complex.mul_im, Complex.div_re, Complex.div_im, Complex.re_ofNat, Complex.im_ofNat,
      Complex.normSq_apply]
    ring
  have hr : (21 / 125 : ℝ) ^ 2 ≤ (1 + (26 / 25 : ℝ) * z.re) ^ 2 :=
    (sq_le_sq₀ (by norm_num only) (by linarith only [hre])).mpr hre.le
  rw [hn]
  rw [Complex.sq_norm, Complex.normSq_apply]
  constructor <;> nlinarith only [hr, hs, sq_nonneg z.im]

/-- The actual fourth-order kernel is complex differentiable throughout the enlarged strip.
Its denominator is nonzero by the quantitative gap, and its exponential numerator is entire.
This proves the additional holomorphy needed to move the left contour to -3/4. -/
theorem fourWide_differentiableAt {z : ℂ} (hz : z ∈ fourWideRegion) :
    DifferentiableAt ℂ rationalPoleFourKernel.function z := by
  have hd : 1 + (26 / 25 : ℂ) * z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have hb := (fourWide_denominator_bounds hz).1
    intro hh
    rw [hh] at hb
    norm_num only at hb
  change
    DifferentiableAt ℂ
      (fun z : ℂ ↦
        (2 * (13 / 25 : ℝ) : ℝ) * Complex.exp (2 * ((14 / 25 : ℝ) : ℂ) * z) /
          (1 + 2 * ((13 / 25 : ℝ) : ℂ) * z) ^ (2 * 2))
      z
  apply
    ((differentiableAt_const _).mul
          (Complex.differentiable_exp.differentiableAt.comp z
            ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul _))).div
      (((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul _).const_add _ |>.pow _) ?_
  apply pow_ne_zero
  convert hd using 1
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, id_eq]

/-- Throughout the extended strip, the actual fourth-order kernel has a uniform quadratic
decay bound with an explicit positive constant. Bound exponential modulation by exp(2)
and use both denominator inequalities to reduce the fourth power to quadratic decay.
The estimate holds without excluding the point -1/2 because this kernel is regular there. -/
theorem fourWide_norm_le {z : ℂ} (hz : z ∈ fourWideRegion) :
    ‖rationalPoleFourKernel.function z‖ ≤
      ((26 / 25 : ℝ) * Real.exp 2 * 100 / (21 / 125 : ℝ) ^ 2) / (1 + ‖z‖ ^ 2) := by
  have hn :
    ‖rationalPoleFourKernel.function z‖ =
      (26 / 25 : ℝ) * Real.exp ((28 / 25 : ℝ) * z.re) / ‖1 + (26 / 25 : ℂ) * z‖ ^ 4 := by
    change ‖Analysis.rationalPoleFunction 2 (13 / 25) (14 / 25) z‖ = _
    simp only [Analysis.rationalPoleFunction, norm_div, norm_mul, Complex.norm_exp, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_div, Complex.ofReal_ofNat]
    norm_num only [Complex.mul_re, Complex.div_re, Complex.div_im, Complex.re_ofNat,
      Complex.im_ofNat, Complex.normSq_apply, mul_zero, zero_mul, sub_zero]
  rw [hn]
  have he : Real.exp ((28 / 25 : ℝ) * z.re) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by linarith only [hz.2])
  have hd := fourWide_denominator_bounds hz
  have hp : 0 < ‖1 + (26 / 25 : ℂ) * z‖ ^ 2 :=
    (by norm_num only : (0 : ℝ) < (21 / 125 : ℝ) ^ 2).trans_le hd.1
  have hmul : (21 / 125 : ℝ) ^ 2 * (1 + ‖z‖ ^ 2) ≤ 100 * ‖1 + (26 / 25 : ℂ) * z‖ ^ 4 := by
    nlinarith only [mul_le_mul_of_nonneg_left hd.2
        (by norm_num only : (0 : ℝ) ≤ (21 / 125 : ℝ) ^ 2),
      mul_le_mul_of_nonneg_left hd.1 (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 100) hp.le)]
  have hnp : 0 < ‖1 + (26 / 25 : ℂ) * z‖ := by
    nlinarith only [hp, norm_nonneg (1 + (26 / 25 : ℂ) * z)]
  have hrec : 1 / ‖1 + (26 / 25 : ℂ) * z‖ ^ 4 ≤ (100 / (21 / 125 : ℝ) ^ 2) / (1 + ‖z‖ ^ 2) := by
    apply (div_le_div_iff₀ (pow_pos hnp 4) (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))).mpr
    rw [one_mul, div_mul_eq_mul_div]
    exact
      (le_div_iff₀ (by norm_num only : (0 : ℝ) < (21 / 125 : ℝ) ^ 2)).mpr (by nlinarith only [hmul])
  calc
    _ ≤ ((26 / 25 : ℝ) * Real.exp 2) / ‖1 + (26 / 25 : ℂ) * z‖ ^ 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num only))
        (pow_nonneg (norm_nonneg _) _)
    _ ≤ _ := by
      have hh :=
        mul_le_mul_of_nonneg_left hrec
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 26 / 25) (Real.exp_pos 2).le)
      convert hh using 1 <;> ring

end PseudoPrime.LLS.PaperStatements
