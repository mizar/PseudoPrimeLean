/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Relative smoothing width and the shifted logarithmic midpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

theorem exp_lower_cutoff : (6100 : ℝ) < Real.exp (35 / 4) := by
  have h := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num only) (by decide : 35 ≠ 0)
  rw [← Real.exp_natCast_mul] at h
  have he : Real.exp (35 / 4) ^ 4 = Real.exp (35 * 1) := by
    rw [← Real.exp_natCast_mul]
    congr 1
    ring
  by_contra! hn
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le hn 4
  rw [he] at hp
  norm_num only at h hp
  linarith only [hp, h]

/-- On the middle band the increasing linear smoothing parameter divided by exp(L/2)
is positive and bounded by its entrance estimate. Use the exponential tangent at 35/4. -/
theorem sinc_relative_width {L : ℝ} (hl : 35 / 2 ≤ L) :
    0 < (2 * L / 7 - 2 / 3) / Real.exp (L / 2) ∧
      (2 * L / 7 - 2 / 3) / Real.exp (L / 2) ≤ 13 / 18300 := by
  have ht : 0 ≤ L / 2 - 35 / 4 := by linarith only [hl]
  have hh := Real.add_one_le_exp (L / 2 - 35 / 4)
  have hp := mul_le_mul exp_lower_cutoff.le hh (by linarith only [ht]) (Real.exp_pos _).le
  rw [← Real.exp_add, add_sub_cancel] at hp
  constructor
  · exact div_pos (by linarith only [hl]) (Real.exp_pos _)
  · apply (div_le_iff₀ (Real.exp_pos _)).2
    linarith only [hl, hp]

/-- The shifted log midpoint lies within 1/2800 of the original log height
whenever the relative width obeys its entrance bound. -/
theorem sinc_log_midpoint_shift {d : ℝ} (hd : 0 ≤ d) (hu : d ≤ 13 / 18300) :
    -(1 / 2800) ≤ Real.log (1 - d / 2) ∧ Real.log (1 - d / 2) ≤ 0 := by
  have hp : 0 < 1 - d / 2 := by linarith only [hu]
  have hi : (1 - d / 2)⁻¹ ≤ 1 + 1 / 2800 := by
    rw [← one_div, div_le_iff₀ hp]
    linarith only [hu]
  exact
    ⟨by linarith only [Real.one_sub_inv_le_log_of_pos hp, hi],
      Real.log_nonpos hp.le (by linarith only [hd])⟩

/-- The true lower smoothing midpoint of exp(L) lies inside the shifted log cell.
The relative width is the one used in the sinc-weighted explicit formula. -/
theorem sinc_midpoint_mem_cell {a b L : ℝ} (ha : 35 / 2 ≤ a) (hL : L ∈ Set.Icc a b) :
    let x := Real.exp L
    let d := (2 * L / 7 - 2 / 3) / Real.exp (L / 2)
    Real.log ((x * (1 - d) + x) / 2) ∈ Set.Icc (a - 1 / 2800) b := by
  let d := (2 * L / 7 - 2 / 3) / Real.exp (L / 2)
  have hd := sinc_relative_width (ha.trans hL.1)
  have hs := sinc_log_midpoint_shift hd.1.le hd.2
  have hp : 0 < 1 - d / 2 := by linarith only [hd.2]
  change Real.log ((Real.exp L * (1 - d) + Real.exp L) / 2) ∈ _
  rw [show (Real.exp L * (1 - d) + Real.exp L) / 2 = Real.exp L * (1 - d / 2) by ring,
    Real.log_mul (Real.exp_pos L).ne' hp.ne', Real.log_exp]
  exact ⟨by linarith only [hL.1, hs.1], by linarith only [hL.2, hs.2]⟩

private theorem exp_upper_cutoff : Real.exp (53 / 4) < 600000 := by
  have h := pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by decide : 53 ≠ 0)
  rw [← Real.exp_natCast_mul] at h
  have he : Real.exp (53 / 4) ^ 4 = Real.exp (53 * 1) := by
    rw [← Real.exp_natCast_mul]
    congr 1
    ring
  by_contra! hn
  have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 600000) hn 4
  rw [he] at hp
  norm_num only at h hp
  linarith only [hp, h]

/-- The logarithmic smoothing parameter stays between the two rational cutoffs
on the entire middle band. The logarithm bounds follow from its tangents at one. -/
theorem sinc_beta_bounds {L : ℝ} (hl : 35 / 2 ≤ L) (hr : L ≤ 53 / 2) :
    let d := (2 * L / 7 - 2 / 3) / Real.exp (L / 2)
    let β := -Real.log (1 - d) / 2
    1 / 300000 ≤ β ∧ β ≤ 1 / 1998 := by
  let d := (2 * L / 7 - 2 / 3) / Real.exp (L / 2)
  have hd := sinc_relative_width hl
  have he :=
    (Real.exp_le_exp.mpr (by linarith only [hr] : L / 2 ≤ 53 / 4)).trans exp_upper_cutoff.le
  have hlo : 1 / 150000 ≤ d := by
    apply (le_div_iff₀ (Real.exp_pos _)).2
    linarith only [he, hl]
  have hp : 0 < 1 - d := by linarith only [hd.2]
  have hi : (1 - d)⁻¹ ≤ 1 + 1 / 999 := by
    rw [← one_div, div_le_iff₀ hp]
    linarith only [hd.2]
  change 1 / 300000 ≤ -Real.log (1 - d) / 2 ∧ -Real.log (1 - d) / 2 ≤ 1 / 1998
  exact
    ⟨by linarith only [Real.log_le_sub_one_of_pos hp, hlo], by
      linarith only [Real.one_sub_inv_le_log_of_pos hp, hi]⟩

/-- The cut height is above the retained zero ledger and its logarithm is at most twelve.
These are the common hypotheses of the moving count error estimate. -/
theorem sinc_cut_height_bounds {β : ℝ} (hl : 1 / 300000 ≤ β) (hr : β ≤ 1 / 1998) :
    let T := (2 / 5) / β
    100 ≤ T ∧ Real.log T ≤ 12 := by
  have hp : 0 < β := by linarith only [hl]
  have ht : (2 / 5) / β ≤ 120000 := (div_le_iff₀ hp).mpr (by linarith only [hl])
  have he := pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num only) (by decide : 12 ≠ 0)
  rw [← Real.exp_natCast_mul] at he
  norm_num only at he
  exact
    ⟨(le_div_iff₀ hp).mpr (by linarith only [hr]),
      (Real.log_le_iff_le_exp (div_pos (by norm_num only) hp)).mpr (by linarith only [ht, he])⟩

/-- The integrated count remainder, midpoint curvature and smoothing boundary errors
together use less than one thousandth in the normalized middle-band estimate. -/
theorem sinc_small_errors {β s : ℝ} (hβ : 0 ≤ β) (hu : β ≤ 1 / 1998) (hs : 6000 ≤ s) :
    19164 / 10 * β ^ 2 + 3640 / (24 * 999 ^ 2) + 2 / s + 1 / (4 * s ^ 2) < 1 / 1000 := by
  have h1 := pow_le_pow_left₀ hβ hu 2
  have h2 :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 2) (by norm_num only : (0 : ℝ) < 6000)
      hs
  have h3 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 6000) hs 2
  have h4 :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1)
      (by norm_num only : (0 : ℝ) < 4 * 6000 ^ 2)
      (mul_le_mul_of_nonneg_left h3 (by norm_num only : (0 : ℝ) ≤ 4))
  linarith only [h1, h2, h4]

/-- The smoothing coefficient is nonnegative and bounded by the scalar phase-grid
parameter throughout the middle band. The lower estimate on beta uses log(1-d) ≤ -d. -/
theorem sinc_log_coefficient {L : ℝ} (hl : 35 / 2 ≤ L) (hr : L ≤ 53 / 2) :
    let q := 2 * L / 7 - 2 / 3
    let d := q / Real.exp (L / 2)
    let β := -Real.log (1 - d) / 2
    0 ≤ -Real.log (2 * Real.pi * β) ∧
      -Real.log (2 * Real.pi * β) ≤ L / 2 - Real.log (Real.pi * q) := by
  intro q d β
  have hd := sinc_relative_width hl
  change 0 < d ∧ d ≤ 13 / 18300 at hd
  have hb := sinc_beta_bounds hl hr
  change 1 / 300000 ≤ β ∧ β ≤ 1 / 1998 at hb
  have hp : 0 < β := by linarith only [hb.1]
  have hq : 0 < q := by
    dsimp only [q]; linarith only [hl]
  have hpos : 0 < 1 - d := by linarith only [hd.2]
  have hw : d ≤ 2 * β := by
    dsimp only [β]; linarith only [Real.log_le_sub_one_of_pos hpos]
  constructor
  · apply neg_nonneg.mpr
    apply Real.log_nonpos (mul_nonneg (mul_nonneg (by norm_num only) Real.pi_pos.le) hp.le)
    nlinarith only [mul_le_mul_of_nonneg_right Real.pi_lt_four.le hp.le, hb.2]
  · have he : Real.pi * q / Real.exp (L / 2) ≤ 2 * Real.pi * β := by
      calc
        _ = Real.pi * d := by
          dsimp only [d]; ring
        _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hw Real.pi_pos.le]
    have hlog := Real.log_le_log (div_pos (mul_pos Real.pi_pos hq) (Real.exp_pos _)) he
    rw [Real.log_div (mul_pos Real.pi_pos hq).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    linarith only [hlog]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
