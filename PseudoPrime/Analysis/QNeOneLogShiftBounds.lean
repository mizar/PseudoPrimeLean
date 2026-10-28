/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.QNeOneHalfShiftBounds
public import PseudoPrime.LLS.Extensions.QNeOneLogShiftSeparation

/-! # Non-one witnesses with a negative logarithmic root correction -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L>=16, the explicit radius L-log L+3 is at least twelve and satisfies
L<=y+log y-2. Apply logarithmic tangent bounds at sixteen and at y.
This converts the implicit analytic allowance into an elementary formula. -/
theorem qNeOneLogShiftRadius_properties {L : ℝ} (hL : (16 : ℝ) ≤ L) :
    12 ≤ L - Real.log L + 3 ∧ L ≤ (L - Real.log L + 3) + Real.log (L - Real.log L + 3) - 2 := by
  have hLp : 0 < L := by linarith only [hL]
  have ht := log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 16) hLp
  have h16 : Real.log 16 < (3 : ℝ) := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hlog : Real.log L ≤ 2 + L / 16 := by linarith only [ht, h16]
  have hy : (12 : ℝ) ≤ L - Real.log L + 3 := by linarith only [hL, hlog]
  have hhalf : L ≤ 2 * (L - Real.log L + 3) := by linarith only [hL, hlog]
  have hyp : 0 < L - Real.log L + 3 := by linarith only [hy]
  have ht2 := log_le_log_add_sub_div hyp hLp
  have hratio : (L - (L - Real.log L + 3)) / (L - Real.log L + 3) ≤ 1 := by
    apply (div_le_one hyp).mpr
    linarith only [hhalf]
  exact ⟨hy, by linarith only [ht2, hratio]⟩

end PseudoPrime.Analysis
