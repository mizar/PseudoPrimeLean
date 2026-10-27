/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ParameterizedThirteenthLogBudget

/-! # Explicit logarithmic normalization for the separated-tail energy bound -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For x>=1, the sixth logarithmic moment is at most 2^16 x.
Use the sixth exponential Taylor term and the convex power sum inequality.
This absorbs the cubic branch's surplus logarithmic powers into one x. -/
theorem one_add_log_six_le {x : ℝ} (hx : 1 ≤ x) : (1 + Real.log x) ^ 6 ≤ 2 ^ 16 * x := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have he := Real.pow_div_factorial_le_exp (Real.log x) hl 6
  rw [Real.exp_log (zero_lt_one.trans_le hx)] at he
  norm_num only [Nat.factorial] at he
  have hp : Real.log x ^ 6 ≤ x * 720 := (div_le_iff₀ (by norm_num only : (0 : ℝ) < 720)).mp he
  have hs := add_pow_le (a := (1 : ℝ)) zero_le_one hl 6
  norm_num only [one_pow] at hs
  nlinarith only [hp, hs, hx]

/-- The normalized cubic alternative E^3<=2^34 p^7 L^4 fits the log10
target, given E<=p^3 and L^6<=2^16p. Raise to the fourth power and multiply
by the elementary energy bound before absorbing the six log powers. -/
theorem log_ten_budget_of_cubic {p E L : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hL : 0 ≤ L) (hEp : E ≤ p ^ 3)
    (hL6 : L ^ 6 ≤ 2 ^ 16 * p) (hc : E ^ 3 ≤ 2 ^ 34 * p ^ 7 * L ^ 4) :
    E ^ 13 ≤ 2 ^ 176 * p ^ 32 * L ^ 10 := by
  have hs := pow_le_pow_left₀ (pow_nonneg hE 3) hc 4
  have hu :=
    mul_le_mul hs hEp hE
      (pow_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2 ^ 34) (pow_nonneg hp 7))
          (pow_nonneg hL 4))
        4)
  have hl :=
    mul_le_mul_of_nonneg_left hL6
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ (2 ^ 34) ^ 4) (pow_nonneg hp 31))
        (pow_nonneg hL 10))
  have hc' :=
    mul_le_mul_of_nonneg_right (by norm_num only : ((2 : ℝ) ^ 34) ^ 4 * 2 ^ 16 ≤ 2 ^ 176)
      (mul_nonneg (pow_nonneg hp 32) (pow_nonneg hL 10))
  nlinarith only [hu, hl, hc']

/-- The separated error branch has T^2 H^4 J^8. Insert the exact third
moment and log-free cutoff coefficients and J<=3L/2; their rational product
is below 2^176. This is the source of the log10 saving. -/
theorem log_ten_budget_of_error {p E T J L : ℝ} (hp : 0 ≤ p) (hT : 0 ≤ T) (hJ : 0 ≤ J) (hL : 0 ≤ L)
    (hTb : T ≤ 786433 * p ^ 3 * L) (hJb : J ≤ (3 / 2 : ℝ) * L)
    (he : E ^ 13 ≤ 10995116277760000 * p ^ 14 * T ^ 2 * (786432 * p ^ 3) ^ 4 * J ^ 8) :
    E ^ 13 ≤ 2 ^ 176 * p ^ 32 * L ^ 10 := by
  have ht := pow_le_pow_left₀ hT hTb 2
  have hj := pow_le_pow_left₀ hJ hJb 8
  have hprod := mul_le_mul ht hj (pow_nonneg hJ 8) (sq_nonneg (786433 * p ^ 3 * L))
  have hs :=
    mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 10995116277760000) (pow_nonneg hp 14))
        (pow_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 786432) (pow_nonneg hp 3)) 4))
  have hc :=
    mul_le_mul_of_nonneg_right
      (by norm_num only : (10995116277760000 : ℝ) * 786433 ^ 2 * 786432 ^ 4 * (3 / 2) ^ 8 ≤ 2 ^ 176)
      (mul_nonneg (pow_nonneg hp 32) (pow_nonneg hL 10))
  nlinarith only [he, hs, hc]

end PseudoPrime.Analysis
