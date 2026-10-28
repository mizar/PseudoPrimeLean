/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneRefinedNumerics

/-! # Common scalar domain for non-one Gamma profiles

Principal, ramp, pole and local budgets hold throughout logarithmic scales at least 35000.
The zero-mass allowance is kept separate for independently certified prefix profiles.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L≥35000, log(L)≤L/3300. Certify log(35000)<21/2 using a Taylor lower bound
 and apply the logarithm tangent bound. This is the common scalar-domain anchor. -/
theorem common_nonOne_ramp_log_bound {L : ℝ} (hL : 35000 ≤ L) : Real.log L ≤ L / 3300 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 35000))
  rw [Real.log_div hL0.ne' (by norm_num only : (35000 : ℝ) ≠ 0)] at ht
  have ha : Real.log (35000 : ℝ) < 21 / 2 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 35000)).mpr
    have he : (271 / 100 : ℝ) ≤ Real.exp 1 :=
      (by norm_num only : (271 / 100 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
    have htay := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) 5
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at htay
    rw [show (21 / 2 : ℝ) = (10 : ℕ) * 1 + 1 / 2 by norm_num only, Real.exp_add, Real.exp_nat_mul]
    have hm :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num only) he 10) htay (by norm_num only)
        (pow_nonneg (Real.exp_pos 1).le 10)
    exact (by norm_num only : (35000 : ℝ) < (271 / 100) ^ 10 * (211 / 128)).trans_le hm
  linarith only [ht, ha, hL]

/-- For L≥35000, the coefficient-0.8 endpoint logarithm is at most L/1650.
 Compare with L² and use the common logarithm bound. This controls principal and local errors. -/
theorem common_nonOne_ramp_endpoint_log_upper {L : ℝ} (hL : 35000 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1650 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only at hc
  linarith only [hc, common_nonOne_ramp_log_bound hL]

/-- For L≥35000, the ramp variation error numerator is at most (693/100)sqrt(x).
 Combine the endpoint and square-root estimates. This fixes the common normalized ramp error. -/
theorem common_nonOne_ramp_error_numerator {L : ℝ} (hL : 35000 ≤ L) :
    (135 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) +
        86 * ((1839 / 1000 : ℝ) * Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) + 21 / 20) ≤
      (693 / 100 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hl := common_nonOne_ramp_endpoint_log_upper hL
  linarith only [hs, hl, hL]

/-- For L≥35000, x=(32/99)L² is at least (17/5)^16.
 Certify the polynomial inequality. This supplies the left-decay anchor for all profiles. -/
theorem common_nonOne_ramp_scale_large {L : ℝ} (hL : 35000 ≤ L) :
    (17 / 5 : ℝ) ^ 16 ≤ (32 / 99 : ℝ) * L ^ 2 := by
  norm_num only
  nlinarith only [hL, sq_nonneg (L - 35000)]

/-- For L≥35000, the principal exponential error is at most (3/20)sqrt(x).
 Use the endpoint logarithm bound. This fixes the common normalized principal error. -/
theorem common_nonOne_exponential_error {L : ℝ} (hL : 35000 ≤ L) :
    Real.sqrt ((32 / 99 : ℝ) * L ^ 2) / 8 +
        (1839 / 1000 : ℝ) * (2 * Real.log ((32 / 99 : ℝ) * L ^ 2) + 3) +
        21 / 10 ≤
      (3 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hx1 : 1 ≤ (32 / 99 : ℝ) * L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 35000)]
  have hc :=
    Real.log_le_log (zero_lt_one.trans_le hx1)
      (show (32 / 99 : ℝ) * L ^ 2 ≤ ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) by nlinarith only [hx1])
  have hl := common_nonOne_ramp_endpoint_log_upper hL
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  linarith only [hc, hl, hs, hL]

/-- For L≥35000, the prime-two logarithmic correction is at most 1/100.
 Clear the positive square-root denominator. This preserves the local budget for every profile. -/
theorem common_nonOne_prime_two_budget {L : ℝ} (hL : 35000 ≤ L) :
    (Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) + Real.log 2) /
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) ≤
      1 / 100 := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hs0 : 0 < Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by linarith only [hs, hL]
  have hl := common_nonOne_ramp_endpoint_log_upper hL
  have h2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  rw [div_le_iff₀ hs0]
  rw [mul_comm (99 / 40 : ℝ)]
  linarith only [hl, hs, h2, hL]

end PseudoPrime.Analysis
