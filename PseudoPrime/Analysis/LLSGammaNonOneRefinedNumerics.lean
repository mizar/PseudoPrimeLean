/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneNumerics
public import PseudoPrime.Analysis.GammaNonOneRefinedNumerics

/-! # Sharper non-one Gamma error budgets

A variable decay anchor and the exact level-four logarithm cost reduce the threshold.
All estimates hold throughout logarithmic scales at least 39400.
-/

@[expose] public section

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
