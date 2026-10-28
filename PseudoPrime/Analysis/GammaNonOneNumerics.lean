/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaVariablePrincipalBounds

/-! # Explicit scalar budgets for the non-one Gamma comparison

At logarithm at least 40000, the ramp error is at most 691/100.
The prime-two correction and variable remainder leave a positive main-term gap.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L≥40000, log(L)≤L/3700. Certify log(40000)<43/4 by a Taylor lower bound,
 then apply log(t)≤t-1 to L/40000. This extends the endpoint logarithm bound to all large L. -/
theorem nonOne_ramp_log_bound {L : ℝ} (hL : 40000 ≤ L) : Real.log L ≤ L / 3700 := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 40000))
  rw [Real.log_div hL0.ne' (by norm_num only : (40000 : ℝ) ≠ 0)] at ht
  have ha : Real.log (40000 : ℝ) < 43 / 4 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 40000)).mpr
    have he : (27 / 10 : ℝ) ≤ Real.exp 1 :=
      (by norm_num only : (27 / 10 : ℝ) ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
    have htay := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) 4
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at htay
    rw [show (43 / 4 : ℝ) = (10 : ℕ) * 1 + 3 / 4 by norm_num only, Real.exp_add, Real.exp_nat_mul]
    have hm :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num only) he 10) htay (by norm_num only)
        (pow_nonneg (Real.exp_pos 1).le 10)
    exact (by norm_num only : (40000 : ℝ) < (27 / 10) ^ 10 * (269 / 128)).trans_le hm
  linarith only [ht, ha, hL]

/-- For L≥40000, the logarithm of the coefficient-0.8 endpoint is at most L/1850.
 Compare the endpoint with L² and apply the uniform logarithm bound.
 This controls the variable principal and prime-two errors. -/
theorem nonOne_ramp_endpoint_log_upper {L : ℝ} (hL : 40000 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1850 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only at hc
  linarith only [hc, nonOne_ramp_log_bound hL]

/-- For L≥40000, the actual ramp variation allowance is at most (691/100)sqrt(x)
 at x=(32/99)L². Combine the endpoint logarithm and square-root lower bounds.
 This improves the rounded error seven while allowing a smaller logarithmic threshold. -/
theorem nonOne_ramp_error_numerator {L : ℝ} (hL : 40000 ≤ L) :
    (135 / 20 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) +
        86 * ((1839 / 1000 : ℝ) * Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) + 21 / 20) ≤
      (691 / 100 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hl := nonOne_ramp_endpoint_log_upper hL
  linarith only [hs, hl, hL]

/-- For L≥40000, x=(32/99)L² is at least 3^16. Certify the quadratic endpoint inequality.
 This supplies the extra-decay gate used to bound the explicit left moment. -/
theorem nonOne_ramp_scale_large {L : ℝ} (hL : 40000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ (32 / 99 : ℝ) * L ^ 2 := by
  norm_num only
  nlinarith only [hL, sq_nonneg (L - 40000)]

/-- For L≥40000, the exponential principal error is at most sqrt(x)/5 at the ramp scale.
 Compare the scale logarithm with the endpoint and use the rational square-root bound.
 This bounds the full principal-series variable error after normalization. -/
theorem nonOne_exponential_error {L : ℝ} (hL : 40000 ≤ L) :
    Real.sqrt ((32 / 99 : ℝ) * L ^ 2) / 8 +
        (1839 / 1000 : ℝ) * (2 * Real.log ((32 / 99 : ℝ) * L ^ 2) + 3) +
        21 / 10 ≤
      (1 / 5 : ℝ) * Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hx1 : 1 ≤ (32 / 99 : ℝ) * L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 40000)]
  have hc :=
    Real.log_le_log (zero_lt_one.trans_le hx1)
      (show (32 / 99 : ℝ) * L ^ 2 ≤ ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) by nlinarith only [hx1])
  have hl := nonOne_ramp_endpoint_log_upper hL
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  linarith only [hc, hl, hs, hL]

/-- For L≥40000, the prime-two logarithmic correction at ramp scale is at most 1/100.
 Clear the positive square root and use log(2)≤1 plus the uniform endpoint logarithm.
 This replaces the level-prime-count cost in the non-one contradiction. -/
theorem nonOne_prime_two_budget {L : ℝ} (hL : 40000 ≤ L) :
    (Real.log ((99 / 40 : ℝ) * ((32 / 99 : ℝ) * L ^ 2)) + Real.log 2) /
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) ≤
      1 / 100 := by
  have hs := ramp_scale_sqrt_lower (show (0 : ℝ) ≤ L by linarith only [hL])
  have hs0 : 0 < Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by linarith only [hs, hL]
  have hl := nonOne_ramp_endpoint_log_upper hL
  have h2 := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
  rw [div_le_iff₀ hs0]
  rw [mul_comm (99 / 40 : ℝ)]
  linarith only [hl, hs, h2, hL]

/-- For positive L, the actual ramp main term exceeds (M+1/795)L.
 Certify the rational squared gap and multiply the proved mass bound by the square root.
 This supplies the strict margin for the improved non-one scalar budget. -/
theorem nonOne_main_term_gap {L : ℝ} (hL : 0 < L) :
    ((11783423 / 25000000 : ℝ) + 1 / 795) * L <
      (2 * (∫ u in (0 : ℝ)..(99 / 40), exponentialRampWeight u) - 1) *
        Real.sqrt ((32 / 99 : ℝ) * L ^ 2) := by
  have hsq :
    ((11783423 / 25000000 : ℝ) + 1 / 795) ^ 2 <
      (83125234337 / 100000000000 : ℝ) ^ 2 * (32 / 99) := by
    norm_num only
  have hc :=
    mul_lt_mul_of_pos_right
      (coefficient_lt_mul_sqrt_of_sq_lt (by norm_num only : (0 : ℝ) ≤ 83125234337 / 100000000000)
        (by norm_num only : (0 : ℝ) ≤ 32 / 99) hsq)
      hL
  have hm :=
    mul_le_mul_of_nonneg_right gamma_ramp_mass_lower (Real.sqrt_nonneg ((32 / 99 : ℝ) * L ^ 2))
  rw [Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 32 / 99), Real.sqrt_sq hL.le] at hm ⊢
  nlinarith only [hc, hm]

end PseudoPrime.Analysis
