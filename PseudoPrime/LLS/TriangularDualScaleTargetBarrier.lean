/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDualScaleInteriorNumerics
public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics

/-!
# Limitation of the ambient dual budget at the coefficient-0.283 target

Verify the logarithmic scale assumptions of the previously proved budget obstruction,
including the exact decimal anchor L=141 log(10).
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For 100≤L≤400 and h≥4, the ambient conductor budget exceeds the ideal
triangular cutoff main term at x=(283/1000)L². Bound x between one and 46000 to
verify 0≤log x≤11, then apply the budget obstruction. This is an interval certificate
for the current comparison, not a lower bound on any least witness. -/
theorem triangular18_dual_interior_ambient_budget_ge_main_of_small_log {L h : ℝ} (hL : 100 ≤ L)
    (hLupper : L ≤ 400) (hh : 4 ≤ h) :
    let x := (283 / 1000) * L ^ 2
    h * (Real.sqrt x * (68 + 4 * Real.exp (-18))) ≤
      (h - 1) * ((72 - Real.log x) * L - 81 + (3 / 2) * Real.log x) := by
  let x := (283 / 1000 : ℝ) * L ^ 2
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 100).trans hL
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    have hl := mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 100) hL
    nlinarith only [hl]
  have hxupper : x ≤ 46000 := by
    dsimp only [x]
    have hl := mul_self_le_mul_self hL0 hLupper
    nlinarith only [hl]
  have hlog :=
    (Real.log_le_log (zero_lt_one.trans_le hx1) hxupper).trans Analysis.log_46000_lt_eleven.le
  exact triangular18_dual_interior_ambient_budget_ge_main hL hh rfl (Real.log_nonneg hx1) hlog

/-- At the exact anchor L=141 log(10) and every h≥4, the ambient conductor
budget exceeds the ideal coefficient-0.283 triangular cutoff main term. Certify
100≤L≤400 using logarithmic bounds for ten, then apply the interval obstruction.
Thus reducing cutoff error alone cannot certify N141 through this ambient budget. -/
theorem triangular18_dual_interior_ambient_budget_ge_main_at_N141 {h : ℝ} (hh : 4 ≤ h) :
    let L := (141 : ℝ) * Real.log 10
    let x := (283 / 1000) * L ^ 2
    h * (Real.sqrt x * (68 + 4 * Real.exp (-18))) ≤
      (h - 1) * ((72 - Real.log x) * L - 81 + (3 / 2) * Real.log x) := by
  have hlower : (100 : ℝ) ≤ 141 * Real.log 10 := by
    linarith only [Analysis.log_ten_gt_twenty_three_tenths]
  have hten : Real.log (10 : ℝ) ≤ 5 / 2 := by
    have h2 := Real.log_two_lt_d9
    have h5 := Real.log_five_lt_d9
    have hm := Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)
    norm_num only at hm
    linarith only [h2, h5, hm]
  have hupper : (141 : ℝ) * Real.log 10 ≤ 400 := by linarith only [hten]
  exact triangular18_dual_interior_ambient_budget_ge_main_of_small_log hlower hupper hh

end PseudoPrime.LLS.PaperStatements
