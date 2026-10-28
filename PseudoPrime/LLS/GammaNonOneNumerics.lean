/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaVariablePrincipalBounds
public import PseudoPrime.Analysis.GammaNonOneNumerics

/-! # Explicit scalar budgets for the non-one Gamma comparison

At logarithm at least 40000, the ramp error is at most 691/100.
The prime-two correction and variable remainder leave a positive main-term gap.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For L≥40000, sqrt(x)≥9L/16 and Q≤L+2, the explicit pole term is at most 21/10.
 Clear the positive denominator and compare rational coefficients.
 This rounds the variable pole error in the non-one witness proof. -/
theorem nonOne_pole_budget {L x Q : ℝ} (hL : 40000 ≤ L) (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x)
    (hQ : Q ≤ L + 2) : ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 21 / 10 := by
  have hs : 0 < Real.sqrt x := by linarith only [hL, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hL, hroot, hQ]

/-- For L≥40000, x≥3^16, sqrt(x)≥9L/16 and 0≤Q≤L+2, the left moment is at most two.
 Retain the extra x^(-1/16) decay and compare rational coefficients.
 This rounds the variable left integral without the former logarithm 46000 gate. -/
theorem nonOne_left_budget {L x Q : ℝ} (hL : 40000 ≤ L) (hx : (3 : ℝ) ^ 16 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ L + 2) :
    x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Q + 283) + 5 / 3) ≤ 2 := by
  have hs : 0 < Real.sqrt x := by linarith only [hroot, hL]
  have hC : 0 ≤ (16 / 5 : ℝ) * (Q + 283) + 5 / 3 := by linarith only [hQ0]
  have hm := mul_le_mul_of_nonneg_right (rpow_neg_nine_sixteenths_le_div_three_sqrt hx) hC
  apply hm.trans
  rw [one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs)]
  nlinarith only [hroot, hL, hQ]

end PseudoPrime.LLS.PaperStatements
