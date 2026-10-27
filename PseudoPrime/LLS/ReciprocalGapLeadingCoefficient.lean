/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapScalarPrefixBounds

/-! # Parameter cost of the current reciprocal-gap zero comparison -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive h,c under the reciprocal-gap zero-comparison constraint
c^2<=1/4+h/2, one has 2c<1+h. Compare squares using h^2>0.
This is a parameter restriction, not a lower bound on actual witnesses. -/
theorem reciprocalGap_comparison_parameter_lt_main_scale {h c : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hb : c ^ 2 ≤ 1 / 4 + h / 2) : 2 * c < 1 + h := by
  have hs : 0 < h ^ 2 := sq_pos_of_pos hh
  have ht : 0 < 1 + h + 2 * c := by linarith only [hh, hc]
  nlinarith only [hs, ht, hb]

/-- For positive h,c satisfying the existing zero-comparison constraint, the squared
ratio (1+h)/(2c) is at least 1+h^2/(1+2h). Compare positive denominators and normalize
the numerator. This exposes the leading-coefficient cost of that comparison when
balancing L/(2c) against sqrt(x)/(1+h); it asserts no witness lower bound. -/
theorem reciprocalGap_leading_coefficient_lower {h c : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hb : c ^ 2 ≤ 1 / 4 + h / 2) : 1 + h ^ 2 / (1 + 2 * h) ≤ (1 + h) ^ 2 / (4 * c ^ 2) := by
  have hd : 0 < 1 + 2 * h := by linarith only [hh]
  have he : 0 < 4 * c ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hc)
  have hm : 4 * c ^ 2 ≤ 1 + 2 * h := by linarith only [hb]
  have hdiv := div_le_div_of_nonneg_left (sq_nonneg (1 + h)) he hm
  have hid : (1 + h) ^ 2 / (1 + 2 * h) = 1 + h ^ 2 / (1 + 2 * h) := by
    field_simp [hd.ne']
    ring
  rw [hid] at hdiv
  exact hdiv

/-- With fixed positive h and an allowed positive c, the leading squared ratio in
the current comparison is strictly greater than one. The explicit excess is positive.
Consequently finite-prefix constant savings alone do not change this coefficient
comparison; varying h or strengthening the comparison is a separate design task. -/
theorem reciprocalGap_leading_coefficient_gt_one {h c : ℝ} (hh : 0 < h) (hc : 0 < c)
    (hb : c ^ 2 ≤ 1 / 4 + h / 2) : 1 < (1 + h) ^ 2 / (4 * c ^ 2) := by
  have hd : 0 < 1 + 2 * h := by linarith only [hh]
  have hs := div_pos (sq_pos_of_pos hh) hd
  have hl := reciprocalGap_leading_coefficient_lower hh hc hb
  linarith only [hs, hl]

end PseudoPrime.LLS.PaperStatements
