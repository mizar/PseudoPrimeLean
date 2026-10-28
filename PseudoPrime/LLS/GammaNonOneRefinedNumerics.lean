/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneNumerics
public import PseudoPrime.Analysis.LLSGammaNonOneRefinedNumerics

/-! # Sharper non-one Gamma error budgets

A variable decay anchor and the exact level-four logarithm cost reduce the threshold.
All estimates hold throughout logarithmic scales at least 39400.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For L≥39400, sqrt(x)≥9L/16 and Q≤L+2, the pole error is at most 21/10.
 Clear the positive denominator. This retains the conductor-uniform pole bound. -/
theorem refined_nonOne_pole_budget {L x Q : ℝ} (hL : 39400 ≤ L)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ : Q ≤ L + 2) :
    ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 21 / 10 := by
  have hs : 0 < Real.sqrt x := by linarith only [hL, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hL, hroot, hQ]

/-- For L≥39400, x≥(17/5)^16 and 0≤Q≤L+2, the left moment is at most 17/10.
 Use the variable decay anchor and sqrt(x)≥9L/16. This sharpens the former bound two. -/
theorem refined_nonOne_left_budget {L x Q : ℝ} (hL : 39400 ≤ L) (hx : (17 / 5 : ℝ) ^ 16 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ L + 2) :
    x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Q + 283) + 5 / 3) ≤ 17 / 10 := by
  have hs : 0 < Real.sqrt x := by linarith only [hroot, hL]
  have hC : 0 ≤ (16 / 5 : ℝ) * (Q + 283) + 5 / 3 := by linarith only [hQ0]
  have hm :=
    mul_le_mul_of_nonneg_right
      (rpow_neg_nine_sixteenths_le_div_scale_sqrt (by norm_num only : (0 : ℝ) < 17 / 5) hx) hC
  apply hm.trans
  rw [one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 17 / 5) hs)]
  nlinarith only [hroot, hL, hQ]

end PseudoPrime.LLS.PaperStatements
