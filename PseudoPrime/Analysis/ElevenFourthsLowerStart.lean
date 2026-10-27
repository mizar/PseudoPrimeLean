/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ElevenFourthsLogShift

/-! # Lower-radius logarithm coupling for the eleven-fourths shift -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Factor 96 as 2^5*3 to express its logarithm using the certified constants
log two and log three. This supports the height and lower logarithm estimates. -/
theorem log_ninety_six_eq : Real.log (96 : ℝ) = 5 * Real.log 2 + Real.log 3 := by
  rw [show (96 : ℝ) = 2 ^ 5 * 3 by norm_num only,
    Real.log_mul (by norm_num only : (2 : ℝ) ^ 5 ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0),
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]

/-- For L>=96, the root L-log L+11/4 is at least 94. Apply a tangent at 96
and certified upper bounds for log two and log three. This lowers the radius
height needed by the continuous branch certificates. -/
theorem elevenFourthsRoot_ge_94 {L : ℝ} (hL : 96 ≤ L) : 94 ≤ L - Real.log L + 11 / 4 := by
  have ht :=
    log_le_log_add_sub_div (a := (96 : ℝ)) (by norm_num only) (by linarith only [hL] : 0 < L)
  rw [log_ninety_six_eq] at ht
  linarith only [ht, hL, Real.log_two_lt_d9, Real.log_three_lt_d9]

/-- For 94<=y<=120, log y is at least 4543/1000+(y-94)/120. First obtain
the lower endpoint at 94 from log 96, then use the tangent from y back to 94
and the upper bound y<=120. This preserves logarithm growth with the radius. -/
theorem log_lower_coupling_of_94_le_le_120 {y : ℝ} (hy : 94 ≤ y) (hy120 : y ≤ 120) :
    4543 / 1000 + (y - 94) / 120 ≤ Real.log y := by
  have ht := log_le_log_add_sub_div (a := (94 : ℝ)) (y := 96) (by norm_num only) (by norm_num only)
  rw [log_ninety_six_eq] at ht
  have h94 : (4543 / 1000 : ℝ) ≤ Real.log 94 := by
    linarith only [ht, Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hy0 : 0 < y := by linarith only [hy]
  have htan := log_le_log_add_sub_div hy0 (by norm_num only : (0 : ℝ) < 94)
  have hm :=
    (le_div_iff₀ hy0).mp (by linarith only [htan, h94] : 4543 / 1000 - Real.log y ≤ (94 - y) / y)
  have hs := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hy120)
  have hcalc : (4543 / 1000 + (y - 94) / 120) * y ≤ Real.log y * y := by nlinarith only [hm, hs]
  exact (mul_le_mul_iff_left₀ hy0).mp hcalc

/-- For positive L and positive root y=L-log L+11/4, the logarithmic tangent
at y gives the stated coupling. This general form has no large-L hypothesis
and supplies the lower-start polynomial comparison. -/
theorem elevenFourthsRoot_tangent_coupling_of_pos {L : ℝ} (hL0 : 0 < L)
    (hy : 0 < L - Real.log L + 11 / 4) :
    let y := L - Real.log L + 11 / 4
    (y - 1) * L ≤ (y - 1) * y + y * (Real.log y - 11 / 4) := by
  have ht := log_le_log_add_sub_div hy hL0
  have hm :=
    (le_div_iff₀ hy).mp
      (by linarith only [ht] :
        Real.log L - Real.log (L - Real.log L + 11 / 4) ≤
          (L - (L - Real.log L + 11 / 4)) / (L - Real.log L + 11 / 4))
  dsimp only
  nlinarith only [hm]

end PseudoPrime.Analysis
