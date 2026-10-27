/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneRefinedNumerics
public import PseudoPrime.LLS.GammaAdaptiveCharacterBounds

/-! # Scalar budgets for the adaptive Gamma zero mass

The improved zero constant allows the non-one comparison at logarithmic scale 37150.
All scalar gates hold throughout the full range above this endpoint.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L≥37150, log(L)≤L/3400. Use the rational anchor and the logarithm tangent bound.
 This controls all larger endpoints without a finite interval assumption. -/
theorem adaptive_nonOne_ramp_log_bound {L : ℝ} (hL : 37150 ≤ L) : Real.log L ≤ L / 3400 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 37150))
  rw [Real.log_div hL0.ne' (by norm_num only : (37150 : ℝ) ≠ 0)] at ht
  have ha : Real.log (37150 : ℝ) < 43 / 4 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 37150)).mpr
    have he : (27 / 10 : ℝ) ≤ Real.exp 1 :=
      (by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
    have htay := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) 4
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at htay
    rw [show (43 / 4 : ℝ) = (10 : ℕ) * 1 + 3 / 4 by norm_num only, Real.exp_add, Real.exp_nat_mul]
    have hm :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num only) he 10) htay (by norm_num only)
        (pow_nonneg (Real.exp_pos 1).le 10)
    exact (by norm_num only : (37150 : ℝ) < (27 / 10) ^ 10 * (269 / 128)).trans_le hm
  linarith only [ht, ha, hL]

/-- For L≥37150, the coefficient-0.8 endpoint logarithm is at most L/1700.
 Compare with L². This controls the principal and prime-two errors. -/
theorem adaptive_nonOne_ramp_endpoint_log_upper {L : ℝ} (hL : 37150 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1700 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only at hc
  linarith only [hc, adaptive_nonOne_ramp_log_bound hL]

/-- For L≥37150, the ramp error numerator is at most (693/100)sqrt(x).
 Use the endpoint logarithm and square-root bounds.
 This supplies the normalized finite-sum error. -/
theorem adaptive_nonOne_ramp_error_numerator {L : ℝ} (hL : 37150 ≤ L) :
    (135 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) +
        86 * ((1839 / 1000 : ℝ) * Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) + 21 / 20) ≤
      (693 / 100 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hl := adaptive_nonOne_ramp_endpoint_log_upper hL
  linarith only [hs, hl, hL]

/-- For L≥37150, the ramp scale is at least (17/5)^16.
 Certify the rational endpoint inequality. This supplies the sharper left-decay anchor. -/
theorem adaptive_nonOne_ramp_scale_large {L : ℝ} (hL : 37150 ≤ L) :
    (17 / 5 : ℝ) ^ 16 ≤ (32 / 99 : ℝ) * L ^ 2 := by
  norm_num only
  nlinarith only [hL, sq_nonneg (L - 37150)]

/-- For L≥37150, the exponential principal error is at most (3/20)sqrt(x).
 Bound its scale logarithm by the endpoint. This preserves the sharper principal budget. -/
theorem adaptive_nonOne_exponential_error {L : ℝ} (hL : 37150 ≤ L) :
    Real.sqrt ((32 / 99 : ℝ) * L ^ 2) / 8 +
        (1839 / 1000 : ℝ) * (2 * Real.log ((32 / 99 : ℝ) * L ^ 2) + 3) +
        21 / 10 ≤
      (3 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hx1 : 1 ≤ (32 / 99 : ℝ) * L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 37150)]
  have hc :=
    Real.log_le_log (zero_lt_one.trans_le hx1)
      (show (32 / 99 : ℝ) * L ^ 2 ≤ ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) by nlinarith only [hx1])
  have hl := adaptive_nonOne_ramp_endpoint_log_upper hL
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  linarith only [hc, hl, hs, hL]

/-- For L≥37150, the prime-two correction is at most 1/100.
 Clear the positive square root and use the endpoint logarithm. This keeps the local budget. -/
theorem adaptive_nonOne_prime_two_budget {L : ℝ} (hL : 37150 ≤ L) :
    (Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) + Real.log 2) /
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) ≤
      1 / 100 := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hs0 : 0 < Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by linarith only [hs, hL]
  have hl := adaptive_nonOne_ramp_endpoint_log_upper hL
  have h2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  rw [div_le_iff₀ hs0]
  rw [mul_comm (99 / 40 : ℝ)]
  linarith only [hl, hs, h2, hL]

end PseudoPrime.Analysis

namespace PseudoPrime.LLS.PaperStatements

/-- For L≥37150, Q≤L+2 and sqrt(x)≥9L/16, the pole term is at most 21/10.
 Compare rational coefficients after clearing the denominator. Use in the adaptive comparison. -/
theorem adaptive_nonOne_pole_budget {L x Q : ℝ} (hL : 37150 ≤ L)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ : Q ≤ L + 2) :
    ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 21 / 10 := by
  have hs : 0 < Real.sqrt x := by linarith only [hL, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hL, hroot, hQ]

/-- For L≥37150, x≥(17/5)^16, Q≤L+2 and sqrt(x)≥9L/16,
 the left moment is at most 17/10. Use the variable decay anchor and its rational budget.
 This closes the contour error in the adaptive witness formula. -/
theorem adaptive_nonOne_left_budget {L x Q : ℝ} (hL : 37150 ≤ L) (hx : (17 / 5 : ℝ) ^ 16 ≤ x)
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
