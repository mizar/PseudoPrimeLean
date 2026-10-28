/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaUniformSignedShiftBounds
public import PseudoPrime.Analysis.GammaUniformSmallScaleNumerics

/-! # Uniform Gamma numerical budgets from scale 224 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For T ≥ 224, sqrt x ≥ 9T/16 and Q ≤ T, the pole error is at most 211/100.
Clear the positive root denominator and compare rational coefficients.
This is the uniform pole allowance for the smaller-scale comparison. -/
theorem gamma_small_scale_pole_budget {T x Q : ℝ} (hT : 224 ≤ T)
    (hroot : (9 / 16 : ℝ) * T ≤ Real.sqrt x) (hQ : Q ≤ T) :
    ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 211 / 100 := by
  have hs : 0 < Real.sqrt x := by linarith only [hT, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hT, hroot, hQ]

/-- For T ≥ 224, x ≥ (9/5)^16, sqrt x ≥ 9T/16 and 0 ≤ Q ≤ T,
the left-contour error is at most eight. Retain the extra real-power decay
and clear the positive denominator. This supplies the smaller-scale contour allowance. -/
theorem gamma_small_scale_left_budget {T x Q : ℝ} (hT : 224 ≤ T) (hx : (9 / 5 : ℝ) ^ 16 ≤ x)
    (hroot : (9 / 16 : ℝ) * T ≤ Real.sqrt x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ T) :
    x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Q + 283) + 5 / 3) ≤ 8 := by
  have hs : 0 < Real.sqrt x := by linarith only [hroot, hT]
  have hC : 0 ≤ (16 / 5 : ℝ) * (Q + 283) + 5 / 3 := by linarith only [hQ0]
  have hm :=
    mul_le_mul_of_nonneg_right
      (rpow_neg_nine_sixteenths_le_div_scale_sqrt (by norm_num only : (0 : ℝ) < 9 / 5) hx) hC
  apply hm.trans
  rw [one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 9 / 5) hs)]
  nlinarith only [hroot, hT, hQ]

end PseudoPrime.LLS.PaperStatements
