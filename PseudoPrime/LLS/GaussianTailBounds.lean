/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.GammaNonOneRefinedNumerics

/-! Explicit Gaussian contour and archimedean tail bounds. -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For r>=100, the contour tail is at most 271/1000 and the archimedean
term is at most 2/1000. Use the rational sixteenth-root anchor 7/4;
this avoids applying the older radius-170 estimate outside its domain. -/
theorem gaussian_tail_of_radius_ge_100 {r : ℝ} (hr : 100 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 271 / 1000 ∧ (512 / 27 : ℝ) / r ^ 2 ≤ 2 / 1000 := by
  have hp : 0 < r := by linarith only [hr]
  have hx : (7 / 4 : ℝ) ^ 16 ≤ r ^ 2 := by
    norm_num only
    nlinarith only [hr]
  have hdec :=
    PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 7 / 4) (by norm_num only) hx
  rw [Real.sqrt_sq hp.le] at hdec
  have hl := mul_le_mul_of_nonneg_left hdec (by norm_num only : (0 : ℝ) ≤ 473 / 10)
  constructor
  · have hc : (473 / 10 : ℝ) / ((7 / 4 : ℝ) * r) ≤ 271 / 1000 := by
      rw [div_le_iff₀ (mul_pos (by norm_num only) hp)]
      nlinarith only [hr]
    have he : (473 / 10 : ℝ) * (1 / ((7 / 4 : ℝ) * r)) = (473 / 10 : ℝ) / ((7 / 4 : ℝ) * r) := by
      ring
    exact (hl.trans_eq he).trans hc
  · rw [div_le_iff₀ (sq_pos_of_pos hp)]
    nlinarith only [hr]

end PseudoPrime.LLS
