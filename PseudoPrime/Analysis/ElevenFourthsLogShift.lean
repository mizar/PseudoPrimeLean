/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealLog
public import PseudoPrime.LLS.FullEndpointShortRange

/-! # Height and tangent coupling for the eleven-fourths logarithmic shift -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At L>=128 the root L-log L+11/4 is at least 120.
Apply the logarithmic tangent at 128 and the certified log-two upper bound.
This provides the radius height for continuous branch separation. -/
theorem elevenFourthsRoot_ge_120 {L : ℝ} (hL : 128 ≤ L) : 120 ≤ L - Real.log L + 11 / 4 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := log_le_log_add_sub_div (a := (128 : ℝ)) (by norm_num only) hL0
  have he : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [he] at ht
  linarith only [ht, Real.log_two_lt_d9, hL]

/-- At y>=120, log y>=19/4. Compare log 128 with log 120 by a tangent
and use the certified lower bound for log two, then logarithmic monotonicity.
This supplies the logarithm height for the shifted certificates. -/
theorem log_ge_nineteen_fourths_of_ge_120 {y : ℝ} (hy : 120 ≤ y) : 19 / 4 ≤ Real.log y := by
  have ht :=
    log_le_log_add_sub_div (a := (120 : ℝ)) (y := 128) (by norm_num only) (by norm_num only)
  have he : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  rw [he] at ht
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 120) hy
  linarith only [ht, hm, Real.log_two_gt_d9]

/-- For L>=128 and positive root y=L-log L+11/4, the logarithmic tangent
at y yields the stated coupling between L,y,log y. Multiply by positive y
and rearrange; this avoids an independent upper estimate for log L. -/
theorem elevenFourthsRoot_tangent_coupling {L : ℝ} (hL : 128 ≤ L)
    (hy : 0 < L - Real.log L + 11 / 4) :
    let y := L - Real.log L + 11 / 4
    (y - 1) * L ≤ (y - 1) * y + y * (Real.log y - 11 / 4) := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := log_le_log_add_sub_div hy hL0
  have hm :=
    (le_div_iff₀ hy).mp
      (by linarith only [ht] :
        Real.log L - Real.log (L - Real.log L + 11 / 4) ≤
          (L - (L - Real.log L + 11 / 4)) / (L - Real.log L + 11 / 4))
  dsimp only
  nlinarith only [hm]

end PseudoPrime.Analysis
