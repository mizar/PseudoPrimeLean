/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogQuadraticRemainder

/-! # A stronger uniform quadratic-logarithm remainder -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonnegative coefficients A,B, a lower height and a logarithmic rectangle
reduce positivity of A*y+C+B*z-2*z² to its rational corner. Bound the negative square
by the upper endpoint. This reusable criterion certifies continuous analytic ranges. -/
theorem log_quadratic_pos_of_rectangle {y z a l u A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hy : a ≤ y)
    (hz : 0 ≤ z) (hl : l ≤ z) (hu : z ≤ u) (hc : 0 < A * a + C + B * l - 2 * u ^ 2) :
    0 < A * y + C + B * z - 2 * z ^ 2 := by
  have hs := mul_self_le_mul_self hz hu
  have ha := mul_le_mul_of_nonneg_left hy hA
  have hb := mul_le_mul_of_nonneg_left hl hB
  linarith only [hs, ha, hb, hc]

/-- For y ≥ 4096, the squared logarithm is at most y/36. Apply the tangent
at 64 to sqrt y and square the nonnegative estimate log y ≤ sqrt y/6.
This controls the unbounded tail of the improved remainder. -/
theorem log_sq_le_thirty_sixth_of_4096 {y : ℝ} (hy : 4096 ≤ y) : (Real.log y) ^ 2 ≤ y / 36 := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hv : 64 ≤ Real.sqrt y := by nlinarith only [hy, Real.sq_sqrt hy0, Real.sqrt_nonneg y]
  have hv0 : 0 < Real.sqrt y := by linarith only [hv]
  have ht := log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 64) hv0
  rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have he : Real.log y = 2 * Real.log (Real.sqrt y) := by
    calc
      Real.log y = Real.log ((Real.sqrt y) ^ 2) := congrArg Real.log (Real.sq_sqrt hy0).symm
      _ = 2 * Real.log (Real.sqrt y) := by
        rw [Real.log_pow]
        norm_num only [Nat.cast_ofNat]
  have hl : Real.log y ≤ Real.sqrt y / 6 := by
    rw [he]
    linarith only [ht, hv, Real.log_two_lt_d9]
  have hs := mul_self_le_mul_self (Real.log_nonneg (by linarith only [hy] : 1 ≤ y)) hl
  nlinarith only [hs, Real.sq_sqrt hy0]

/-- For a natural exponent k, bound log(3*2^k) by 11/10+(7/10)k.
Use the certified logarithms of two and three. This supplies the two short
rectangle endpoints needed below without new transcendental certificates. -/
theorem log_three_mul_two_pow_le (k : ℕ) :
    Real.log (3 * (2 : ℝ) ^ k) ≤ 11 / 10 + (7 / 10 : ℝ) * k := by
  rw [Real.log_mul (by norm_num only : (3 : ℝ) ≠ 0)
      (pow_ne_zero k (by norm_num only : (2 : ℝ) ≠ 0)),
    Real.log_pow]
  have htwo : Real.log (2 : ℝ) ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith only [hm, Real.log_three_lt_d9]

/-- For every y ≥ 94, the improved remainder (17/200)y+14+(69/10)log y-2(log y)²
is positive. Certify eight real rectangles below 4096 and bound the remaining
half-line by the square-root tangent. No input integers are enumerated. -/
theorem sharpLogQuadraticRemainder_pos_of_94 {y : ℝ} (hy : 94 ≤ y) :
    0 < (17 / 200 : ℝ) * y + 14 + (69 / 10 : ℝ) * Real.log y - 2 * (Real.log y) ^ 2 := by
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hz := Real.log_nonneg hy1
  by_cases h128 : y ≤ 128
  · have ha : (94 : ℝ) ≤ y := by linarith only [hy]
    have hd :=
      log_dyadic_bounds (a := 6) (b := 7)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 6 ≤ y)
        (by
          norm_num only; linarith only [h128] : y ≤ (2 : ℝ) ^ 7)
    norm_num only [Nat.cast_ofNat] at hd
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hd.2
        (by norm_num only)
  by_cases h192 : y ≤ 192
  · have ha : (128 : ℝ) ≤ y := by linarith only [h128]
    have hd :=
      log_dyadic_bounds (a := 7) (b := 8)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 7 ≤ y)
        (by
          norm_num only; linarith only [h192] : y ≤ (2 : ℝ) ^ 8)
    norm_num only [Nat.cast_ofNat] at hd
    have hu : Real.log y ≤ 53 / 10 := by
      have ht := log_three_mul_two_pow_le 6
      norm_num only at ht
      have hl := Real.log_le_log hy0 h192
      linarith only [ht, hl]
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hu
        (by norm_num only)
  by_cases h256 : y ≤ 256
  · have ha : (192 : ℝ) ≤ y := by linarith only [h192]
    have hd :=
      log_dyadic_bounds (a := 7) (b := 8)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 7 ≤ y)
        (by
          norm_num only; linarith only [h256] : y ≤ (2 : ℝ) ^ 8)
    norm_num only [Nat.cast_ofNat] at hd
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hd.2
        (by norm_num only)
  by_cases h384 : y ≤ 384
  · have ha : (256 : ℝ) ≤ y := by linarith only [h256]
    have hd :=
      log_dyadic_bounds (a := 8) (b := 9)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 8 ≤ y)
        (by
          norm_num only; linarith only [h384] : y ≤ (2 : ℝ) ^ 9)
    norm_num only [Nat.cast_ofNat] at hd
    have hu : Real.log y ≤ 6 := by
      have ht := log_three_mul_two_pow_le 7
      norm_num only at ht
      have hl := Real.log_le_log hy0 h384
      linarith only [ht, hl]
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hu
        (by norm_num only)
  by_cases h512 : y ≤ 512
  · have ha : (384 : ℝ) ≤ y := by linarith only [h384]
    have hd :=
      log_dyadic_bounds (a := 8) (b := 9)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 8 ≤ y)
        (by
          norm_num only; linarith only [h512] : y ≤ (2 : ℝ) ^ 9)
    norm_num only [Nat.cast_ofNat] at hd
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hd.2
        (by norm_num only)
  by_cases h1024 : y ≤ 1024
  · have ha : (512 : ℝ) ≤ y := by linarith only [h512]
    have hd :=
      log_dyadic_bounds (a := 9) (b := 10)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 9 ≤ y)
        (by
          norm_num only; linarith only [h1024] : y ≤ (2 : ℝ) ^ 10)
    norm_num only [Nat.cast_ofNat] at hd
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hd.2
        (by norm_num only)
  by_cases h2048 : y ≤ 2048
  · have ha : (1024 : ℝ) ≤ y := by linarith only [h1024]
    have hd :=
      log_dyadic_bounds (a := 10) (b := 11)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 10 ≤ y)
        (by
          norm_num only; linarith only [h2048] : y ≤ (2 : ℝ) ^ 11)
    norm_num only [Nat.cast_ofNat] at hd
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hd.2
        (by norm_num only)
  by_cases h4096 : y ≤ 4096
  · have ha : (2048 : ℝ) ≤ y := by linarith only [h2048]
    have hd :=
      log_dyadic_bounds (a := 11) (b := 12)
        (by
          norm_num only; linarith only [ha] : (2 : ℝ) ^ 11 ≤ y)
        (by
          norm_num only; linarith only [h4096] : y ≤ (2 : ℝ) ^ 12)
    norm_num only [Nat.cast_ofNat] at hd
    exact
      log_quadratic_pos_of_rectangle (by norm_num only) (by norm_num only) ha hz hd.1 hd.2
        (by norm_num only)
  have hs := log_sq_le_thirty_sixth_of_4096 (by linarith only [h4096])
  linarith only [hs, hz, hy]

end PseudoPrime.Analysis
