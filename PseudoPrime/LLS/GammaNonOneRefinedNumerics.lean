/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneNumerics

/-! # Sharper non-one Gamma error budgets

A variable decay anchor and the exact level-four logarithm cost reduce the threshold.
All estimates hold throughout logarithmic scales at least 39400.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive a and x≥a^16, the left-line decay is at most 1/(a sqrt(x)).
 Separate the exponents and use monotonicity of the negative real power.
 This allows a sharper decay anchor than the fixed integer three. -/
theorem rpow_neg_nine_sixteenths_le_div_scale_sqrt {a x : ℝ} (ha : 0 < a) (hx : a ^ (16 : ℕ) ≤ x) :
    x ^ (-9 / 16 : ℝ) ≤ 1 / (a * Real.sqrt x) := by
  have hxpos := (pow_pos ha 16).trans_le hx
  have hsmall :=
    Real.rpow_le_rpow_of_nonpos (pow_pos ha 16) hx (by norm_num only : (-1 / 16 : ℝ) ≤ 0)
  have hbase : (a ^ (16 : ℕ)) ^ (-1 / 16 : ℝ) = 1 / a := by
    rw [← Real.rpow_natCast_mul ha.le]
    norm_num only [Real.rpow_neg_one, one_div]
  have hhalf : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [neg_div, Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hbase] at hsmall
  calc
    _ = x ^ (-1 / 16 : ℝ) * x ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num only
    _ ≤ (1 / a) * (1 / Real.sqrt x) := by
      rw [hhalf]
      exact mul_le_mul_of_nonneg_right hsmall (div_nonneg zero_le_one (Real.sqrt_nonneg x))
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.Analysis

/-- The level-four logarithm cost is at most 7/5. Bound exp(7/5) from below by a
 finite Taylor sum and the certified exp(1) bound. This retains a smaller conductor cost. -/
theorem log_four_le_seven_fifths : Real.log (4 : ℝ) ≤ 7 / 5 := by
  apply (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 4)).mpr
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 :=
    (by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2 / 5) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ht
  rw [show (7 / 5 : ℝ) = 1 + 2 / 5 by norm_num only, Real.exp_add]
  have hm := mul_le_mul he ht (by norm_num only) (Real.exp_pos 1).le
  exact (by norm_num only : (4 : ℝ) ≤ (27 / 10) * (559 / 375)).trans hm

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For L≥39400, log(L)≤L/3650. Use the certified anchor logarithm and log(t)≤t-1.
 This uniformly controls the endpoint logarithm at the reduced threshold. -/
theorem refined_nonOne_ramp_log_bound {L : ℝ} (hL : 39400 ≤ L) : Real.log L ≤ L / 3650 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 39400))
  rw [Real.log_div hL0.ne' (by norm_num only : (39400 : ℝ) ≠ 0)] at ht
  have ha : Real.log (39400 : ℝ) < 43 / 4 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 39400)).mpr
    have he : (27 / 10 : ℝ) ≤ Real.exp 1 :=
      (by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
    have htay := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) 4
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at htay
    rw [show (43 / 4 : ℝ) = (10 : ℕ) * 1 + 3 / 4 by norm_num only, Real.exp_add, Real.exp_nat_mul]
    have hm :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num only) he 10) htay (by norm_num only)
        (pow_nonneg (Real.exp_pos 1).le 10)
    exact (by norm_num only : (39400 : ℝ) < (27 / 10) ^ 10 * (269 / 128)).trans_le hm
  linarith only [ht, ha, hL]

/-- For L≥39400, the coefficient-0.8 endpoint logarithm is at most L/1825.
 Compare with L² and apply the logarithm bound. Use this in the principal and local errors. -/
theorem refined_nonOne_ramp_endpoint_log_upper {L : ℝ} (hL : 39400 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1825 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only at hc
  linarith only [hc, refined_nonOne_ramp_log_bound hL]

/-- For L≥39400, the normalized ramp error allowance is at most 691/100.
 Combine the endpoint logarithm and square-root estimates before normalization.
 This retains the lower finite sum's explicit numerical budget. -/
theorem refined_nonOne_ramp_error_numerator {L : ℝ} (hL : 39400 ≤ L) :
    (135 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) +
        86 * ((1839 / 1000 : ℝ) * Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) + 21 / 20) ≤
      (691 / 100 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hl := refined_nonOne_ramp_endpoint_log_upper hL
  linarith only [hs, hl, hL]

/-- For L≥39400, the ramp scale is at least (17/5)^16. Certify the rational polynomial
 inequality. This supplies the sharper variable decay anchor for the left moment. -/
theorem refined_nonOne_ramp_scale_large {L : ℝ} (hL : 39400 ≤ L) :
    (17 / 5 : ℝ) ^ 16 ≤ (32 / 99 : ℝ) * L ^ 2 := by
  norm_num only
  nlinarith only [hL, sq_nonneg (L - 39400)]

/-- For L≥39400, the exponential principal error is at most (3/20)sqrt(x).
 Control the scale logarithm by the endpoint. This improves the normalized principal budget. -/
theorem refined_nonOne_exponential_error {L : ℝ} (hL : 39400 ≤ L) :
    Real.sqrt ((32 / 99 : ℝ) * L ^ 2) / 8 +
        (1839 / 1000 : ℝ) * (2 * Real.log ((32 / 99 : ℝ) * L ^ 2) + 3) +
        21 / 10 ≤
      (3 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hx1 : 1 ≤ (32 / 99 : ℝ) * L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 39400)]
  have hc :=
    Real.log_le_log (zero_lt_one.trans_le hx1)
      (show (32 / 99 : ℝ) * L ^ 2 ≤ ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) by nlinarith only [hx1])
  have hl := refined_nonOne_ramp_endpoint_log_upper hL
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  linarith only [hc, hl, hs, hL]

/-- For L≥39400, the remaining prime-two correction at ramp scale is at most 1/100.
 Use log(2)≤1 and clear the positive square root. This includes the odd-power endpoint. -/
theorem refined_nonOne_prime_two_budget {L : ℝ} (hL : 39400 ≤ L) :
    (Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) + Real.log 2) /
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) ≤
      1 / 100 := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hs0 : 0 < Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by linarith only [hs, hL]
  have hl := refined_nonOne_ramp_endpoint_log_upper hL
  have h2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  rw [div_le_iff₀ hs0]
  rw [mul_comm (99 / 40 : ℝ)]
  linarith only [hl, hs, h2, hL]

end PseudoPrime.Analysis

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
