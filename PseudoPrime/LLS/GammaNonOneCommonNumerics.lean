/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneRefinedNumerics
public import PseudoPrime.Analysis.GammaNonOneCommonNumerics

/-! # Common scalar domain for non-one Gamma profiles

Principal, ramp, pole and local budgets hold throughout logarithmic scales at least 35000.
The zero-mass allowance is kept separate for independently certified prefix profiles.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For L≥35000, Q≤L+2 and sqrt(x)≥9L/16, the pole budget is at most 21/10.
 Compare rational coefficients after clearing the denominator. This is profile-independent. -/
theorem common_nonOne_pole_budget {L x Q : ℝ} (hL : 35000 ≤ L)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ : Q ≤ L + 2) :
    ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 21 / 10 := by
  have hs : 0 < Real.sqrt x := by linarith only [hL, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hL, hroot, hQ]

/-- For L≥35000, x≥(17/5)^16, Q≤L+2 and sqrt(x)≥9L/16,
 the left-moment budget is at most 17/10. Retain the extra real-power decay.
 This supplies the common contour-left error. -/
theorem common_nonOne_left_budget {L x Q : ℝ} (hL : 35000 ≤ L) (hx : (17 / 5 : ℝ) ^ 16 ≤ x)
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
