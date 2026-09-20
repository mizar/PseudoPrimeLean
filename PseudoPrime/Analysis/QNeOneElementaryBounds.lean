/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Analysis.ElementaryBounds
import PseudoPrime.Analysis.LogarithmicConstants
import Mathlib.Tactic

/-!
# Elementary logarithmic and rational inequalities

These real-variable identities and inequalities bound logarithmic numerators, reciprocal-square
factors, and polynomial gaps. They require no characters or L-functions. The estimates use
explicit bounds on logarithms and positive powers of the radius to control rational expressions.
-/

namespace PseudoPrime.Analysis

/-- The two bounded logarithmic constants contribute nonnegative errors to the numerator gap. -/
lemma log_constant_error_sum_nonneg {y : ℝ} (hy : 48 ≤ y) :
    0 ≤
      5 * (y ^ 2 - 1) * (39 / 100 - (Real.log 4 - Real.log Real.pi)) +
        10 * y ^ 2 * (347 / 500 - Real.log 2) := by
  have hA :=
    sub_nonneg.mpr
      ((sub_le_sub zeroStar_log_four_upper zeroStar_log_pi_lower).trans_eq
        (by norm_num only : (139 / 100 : ℝ) - 1 = 39 / 100))
  have hB :=
    sub_nonneg.mpr (Real.log_two_lt_d9.le.trans (by norm_num only : (0.6931471808 : ℝ) ≤ 347 / 500))
  exact
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (zeroStar_square_sub_one_nonneg hy)) hA)
      (mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg y)) hB)

/-- The quadratic part of the numerator gap is nonnegative above `48`. -/
lemma quadratic_gap_nonneg_of_forty_eight_le {y : ℝ} (hy : 48 ≤ y) :
    0 ≤ 311 / 100 * y * (y - 48) + 2482 / 25 * y := by
  have hy0 : 0 ≤ y := (by norm_num only : (0 : ℝ) ≤ 48).trans hy
  exact
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hy0) (sub_nonneg.mpr hy))
      (mul_nonneg (by norm_num only) hy0)

/-- The remaining logarithmic term and constant in the numerator gap are nonnegative. -/
lemma log_remainder_nonneg_of_forty_eight_le {y : ℝ} (hy : 48 ≤ y) :
    0 ≤ 20 * (2 * (y - 1) + 1) * Real.log y + 639 / 20 := by
  have hy1 : 1 ≤ y := (by norm_num only : (1 : ℝ) ≤ 48).trans hy
  exact
    add_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num only)
          (add_nonneg (mul_nonneg (by norm_num only) (sub_nonneg.mpr hy1)) zero_le_one))
        (Real.log_nonneg hy1))
      (by norm_num only)

/-- Clearing the reciprocal denominator reduces the bound to this explicit polynomial gap. -/
lemma reciprocal_log_numerator_polynomial_le {y : ℝ} (hy : 48 ≤ y) :
    (y ^ 2 - 1) * (y + Real.log 4 - Real.log Real.pi) * 5 - 2 * y ^ 2 * 4 -
        2 * y ^ 2 * (2 * 5 * Real.log y - 8 - 5 * Real.log 2) ≤
      5 * (y - 2 ^ 2 * Real.log y + 2 * 3) * (y - 1) ^ 2 := by
  have hcert :=
    add_nonneg (log_constant_error_sum_nonneg hy)
      (add_nonneg (quadratic_gap_nonneg_of_forty_eight_le hy)
        (log_remainder_nonneg_of_forty_eight_le hy))
  apply sub_nonneg.mp
  exact hcert.trans_eq (by ring)

/-- Clear the numerator by distributing its square multiplier and cancelling one reciprocal. -/
lemma reciprocal_log_numerator_mul_sq {y L A B C : ℝ} (hy : y ≠ 0) :
    (1 / 2 * (1 - 1 / y ^ 2) * (y + A - B) - 4 / 5 - (2 * L - 8 / 5 - C)) * y ^ 2 =
      ((y ^ 2 - 1) * (y + A - B) * 5 - 2 * y ^ 2 * 4 - 2 * y ^ 2 * (2 * 5 * L - 8 - 5 * C)) /
        10 := by
  have hc : (1 - 1 / y ^ 2) * y ^ 2 = y ^ 2 - 1 := by
    rw [sub_mul, one_mul, one_div_mul_cancel (pow_ne_zero 2 hy)]
  calc
    _ = ((1 - 1 / y ^ 2) * y ^ 2) * (y + A - B) / 2 - (4 / 5 + (2 * L - 8 / 5 - C)) * y ^ 2 := by
      ring
    _ = _ := by
      rw [hc]; ring

/-- Multiplication by `y²` turns the affine product into the matching polynomial. -/
lemma affine_reciprocal_factor_mul_sq {y L : ℝ} (hy : y ≠ 0) :
    ((y / 2 - 2 * L + 3) * (1 - 1 / y) ^ 2) * y ^ 2 =
      (5 * (y - 2 ^ 2 * L + 2 * 3) * (y - 1) ^ 2) / 10 := by
  rw [mul_assoc, zeroStar_den_mul_sq hy]
  ring

/-- The reciprocal numerator is bounded by the affine expression on the tail. -/
lemma reciprocal_log_quotient_le_affine {y : ℝ} (hy : 48 ≤ y) :
    ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2 ≤
      y / 2 - 2 * Real.log y + 3 := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy
  apply (div_le_iff₀ (zeroStar_den_pos hy hypos)).2
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hypos)).mp
  rw [reciprocal_log_numerator_mul_sq hypos.ne', affine_reciprocal_factor_mul_sq hypos.ne']
  exact div_le_div_of_nonneg_right (reciprocal_log_numerator_polynomial_le hy) (by norm_num only)

/-- The affine gap is strictly positive whenever the tail logarithmic lower bound holds. -/
lemma affine_log_gap_pos {y L : ℝ} (hy : 0 ≤ y) (hL : 73 / 20 ≤ L) :
    0 < (600 * y + 1200 * L + 2610) * (L - 73 / 20) + 14273 / 2 := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 73 / 20).trans hL
  have hc :=
    add_nonneg
      (add_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 600) hy)
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1200) hL0))
      (by norm_num only : (0 : ℝ) ≤ 2610)
  exact add_pos_of_nonneg_of_pos (mul_nonneg hc (sub_nonneg.mpr hL)) (by norm_num only)

/-- For `y ≥ 8`, `3q ≤ l ≤ y/8 + 3q - 1`, and `0.69 ≤ q ≤ 0.7`, the stated rational
coefficient is nonnegative. Clearing the positive powers of `y` reduces the claim to polynomial
inequalities. This public certificate supports logarithmic coefficient comparisons. -/
lemma reciprocal_square_coefficient_nonneg {y l q : ℝ} (hy : 8 ≤ y) (hl : l ≤ y / 8 + 3 * q - 1)
    (hlower : 3 * q ≤ l) (hq1 : 0.69 ≤ q) (hq2 : q ≤ 0.7) (hpy : 0 < y) :
    0 ≤
      0.45 - q + 1.098 / 2 - (l + 1) / y + (8 * l - 11 / 4 - 1.4 / 2) / y ^ 2 +
        (-5 * l + 5 / 2) / y ^ 3 := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hpy
  have hy3 : 0 < y ^ 3 := pow_pos hpy 3
  have hP : 0 ≤ 8 * l - 11 / 4 - 1.4 / 2 := by linarith
  have hR : -5 * (y / 8 + 3 * q - 1) + 5 / 2 ≤ -5 * l + 5 / 2 := by
    have hmul := mul_le_mul_of_nonpos_left hl (show (-5 : ℝ) ≤ 0 by norm_num only)
    linarith
  have hC : 0.299 ≤ 0.45 - q + 1.098 / 2 := by linarith
  have hC0 : 0 ≤ 0.45 - q + 1.098 / 2 := by linarith
  have hq2y2 : q * y ^ 2 ≤ 0.7 * y ^ 2 := mul_le_mul_of_nonneg_right hq2 (le_of_lt hy2)
  have hq2y3 : q * y ^ 3 ≤ 0.7 * y ^ 3 := mul_le_mul_of_nonneg_right hq2 (le_of_lt hy3)
  field_simp
  nlinarith only [hy, hl, hlower, hq1, hq2, hpy, hy2, hy3, hP, hR, hC, hC0, hq2y2, hq2y3,
    mul_nonneg hC0 (le_of_lt hy3), mul_nonneg hP (le_of_lt hy2)]

/-- For `y ≥ 8`, `3q ≤ l ≤ y/8 + 3q - 1`, and `0.69 ≤ q ≤ 0.7`, the stated rational
coefficient is nonnegative. Clearing the positive powers of `y` reduces the claim to polynomial
inequalities. This public certificate supports logarithmic coefficient comparisons. -/
lemma reciprocal_square_coefficient_nonneg_explicit {y l q : ℝ} (hy : 8 ≤ y)
    (hl : l ≤ y / 8 + 3 * q - 1) (hlower : 3 * q ≤ l) (hq1 : 0.69 ≤ q) (hq2 : q ≤ 0.7)
    (hpy : 0 < y) :
    0 ≤
      0.45 - q + 1.098 / 2 - (l + 1) / y + (8 * l - 11 / 4 - 1.4 / 2) / y ^ 2 +
        (-5 * l + 5 / 2) / y ^ 3 := by
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hpy
  have hy3 : 0 < y ^ 3 := pow_pos hpy 3
  have hP : 0 ≤ 8 * l - 11 / 4 - 1.4 / 2 := by nlinarith only [hlower, hq1]
  have hR : -5 * (y / 8 + 3 * q - 1) + 5 / 2 ≤ -5 * l + 5 / 2 := by
    have hmul := mul_le_mul_of_nonpos_left hl (show (-5 : ℝ) ≤ 0 by norm_num only)
    simpa only [add_comm] using add_le_add_right hmul (5 / 2 : ℝ)
  have hC : 0.299 ≤ 0.45 - q + 1.098 / 2 := by nlinarith only [hq2]
  have hC0 : 0 ≤ 0.45 - q + 1.098 / 2 := le_trans (by norm_num only) hC
  have hq2y2 : q * y ^ 2 ≤ 0.7 * y ^ 2 := mul_le_mul_of_nonneg_right hq2 (le_of_lt hy2)
  have hq2y3 : q * y ^ 3 ≤ 0.7 * y ^ 3 := mul_le_mul_of_nonneg_right hq2 (le_of_lt hy3)
  field_simp
  nlinarith [mul_nonneg hC0 (le_of_lt hy3), mul_nonneg hP (le_of_lt hy2)]

/-- For a natural number `B ≥ 10`, `5 < (log B)^2`.
Logarithmic monotonicity and explicit lower bounds for `log 2` and `log 5` prove the claim.
This numerical estimate allows a constant bound of five to be absorbed into a logarithmic square. -/
lemma five_lt_log_sq_of_ten_le {B : ℕ} (hB : 10 ≤ B) : (5 : ℝ) < (Real.log (B : ℝ)) ^ 2 := by
  have hBreal : (10 : ℝ) ≤ B := by exact_mod_cast hB
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 10)
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 10) hBreal) hBreal
  rw [show (10 : ℝ) = 2 * 5 by norm_num only,
    Real.log_mul (by norm_num only) (by norm_num only)] at hlog
  nlinarith only [hlog, Real.log_two_gt_d9, Real.log_five_gt_d9,
    sq_nonneg (Real.log (B : ℝ) - (23 / 10 : ℝ))]

end PseudoPrime.Analysis
