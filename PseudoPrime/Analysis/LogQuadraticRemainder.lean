/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import PseudoPrime.Analysis.RealLog

/-! # A uniform positive quadratic-logarithm remainder -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive coordinate between 2^a and 2^b, log y lies between
(69/100)a and (7/10)b. Apply logarithmic monotonicity and the certified log-two bounds.
This supplies reusable rectangle data without new transcendental certificates. -/
theorem log_dyadic_bounds {y : ℝ} {a b : ℕ} (ha : (2 : ℝ) ^ a ≤ y) (hb : y ≤ (2 : ℝ) ^ b) :
    (a : ℝ) * (69 / 100) ≤ Real.log y ∧ Real.log y ≤ (b : ℝ) * (7 / 10) := by
  have hy0 : 0 < y := (pow_pos (by norm_num only : (0 : ℝ) < 2) a).trans_le ha
  have hl := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 2) a) ha
  have hu := Real.log_le_log hy0 hb
  rw [Real.log_pow] at hl hu
  have hA := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
  have hB := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  constructor
  · nlinarith only [hl, hA, Nat.cast_nonneg (α := ℝ) a]
  · nlinarith only [hu, hB, Nat.cast_nonneg (α := ℝ) b]

/-- For y at least 1024, (log y)^2 is at most y/16. Apply the logarithmic
tangent at 32 to sqrt y, then square nonnegative bounds. This controls the infinite
tail of the quadratic-logarithm remainder by an elementary linear function. -/
theorem log_sq_le_sixteenth_of_1024 {y : ℝ} (hy : 1024 ≤ y) : (Real.log y) ^ 2 ≤ y / 16 := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hv : 32 ≤ Real.sqrt y := by nlinarith only [hy, Real.sq_sqrt hy0, Real.sqrt_nonneg y]
  have hv0 : 0 < Real.sqrt y := by linarith only [hv]
  have ht := log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 32) hv0
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow] at ht
  norm_num only [Nat.cast_ofNat] at ht
  have he : Real.log y = 2 * Real.log (Real.sqrt y) := by
    calc
      Real.log y = Real.log ((Real.sqrt y) ^ 2) := congrArg Real.log (Real.sq_sqrt hy0).symm
      _ = 2 * Real.log (Real.sqrt y) := by
        rw [Real.log_pow]
        norm_num only [Nat.cast_ofNat]
  have hl : Real.log y ≤ Real.sqrt y / 4 := by
    rw [he]
    linarith only [ht, hv, Real.log_two_lt_d9]
  have hs := mul_self_le_mul_self (Real.log_nonneg (by linarith only [hy] : 1 ≤ y)) hl
  nlinarith only [hs, Real.sq_sqrt hy0]

/-- For y>=a and 0<=z between l and u, positivity of the rational corner
(13/100)a+14+7l-2u^2 implies positivity at (y,z). Bound the negative square by u^2.
This is the generic rectangle certificate used for the bounded analytic ranges. -/
theorem logQuadraticRemainder_pos_of_rectangle {y z a l u : ℝ} (hy : a ≤ y) (hz0 : 0 ≤ z)
    (hzl : l ≤ z) (hzu : z ≤ u) (hcert : 0 < (13 / 100 : ℝ) * a + 14 + 7 * l - 2 * u ^ 2) :
    0 < (13 / 100 : ℝ) * y + 14 + 7 * z - 2 * z ^ 2 := by
  have hs := mul_self_le_mul_self hz0 hzu
  linarith only [hy, hzl, hs, hcert]

/-- For every real y at least 94, (13/100)y+14+7log y-2(log y)^2 is positive.
Use four dyadic logarithmic rectangles below 1024 and the uniform square-logarithm
tail above it. This certifies an entire half-line without enumerating input moduli. -/
theorem logQuadraticRemainder_pos_of_94 {y : ℝ} (hy : 94 ≤ y) :
    0 < (13 / 100 : ℝ) * y + 14 + 7 * Real.log y - 2 * (Real.log y) ^ 2 := by
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hz0 := Real.log_nonneg hy1
  by_cases h128 : y ≤ 128
  · have hd :=
      log_dyadic_bounds (a := 6) (b := 7)
        (by
          norm_num only; linarith only [hy] : (2 : ℝ) ^ 6 ≤ y)
        (by
          norm_num only; exact h128 : y ≤ (2 : ℝ) ^ 7)
    norm_num only [Nat.cast_ofNat] at hd
    exact
      logQuadraticRemainder_pos_of_rectangle hy hz0 (by linarith only [hd.1] : (4 : ℝ) ≤ Real.log y)
        (by linarith only [hd.2] : Real.log y ≤ (5 : ℝ)) (by norm_num only)
  · by_cases h200 : y ≤ 200
    · have hd :=
        log_dyadic_bounds (a := 7) (b := 8)
          (by
            norm_num only; linarith only [h128] : (2 : ℝ) ^ 7 ≤ y)
          (by
            norm_num only; linarith only [h200] : y ≤ (2 : ℝ) ^ 8)
      norm_num only [Nat.cast_ofNat] at hd
      exact
        logQuadraticRemainder_pos_of_rectangle (by linarith only [h128] : (128 : ℝ) ≤ y) hz0
          (by linarith only [hd.1] : (24 / 5 : ℝ) ≤ Real.log y)
          (by linarith only [hd.2] : Real.log y ≤ (28 / 5 : ℝ)) (by norm_num only)
    · by_cases h400 : y ≤ 400
      · have hd :=
          log_dyadic_bounds (a := 7) (b := 9)
            (by
              norm_num only; linarith only [h200] : (2 : ℝ) ^ 7 ≤ y)
            (by
              norm_num only; linarith only [h400] : y ≤ (2 : ℝ) ^ 9)
        norm_num only [Nat.cast_ofNat] at hd
        have hlog400 : Real.log (400 : ℝ) < 6 := by
          rw [show (400 : ℝ) = 2 ^ 4 * 5 ^ 2 by norm_num only,
            Real.log_mul (by norm_num only : (2 : ℝ) ^ 4 ≠ 0) (by norm_num only : (5 : ℝ) ^ 2 ≠ 0),
            Real.log_pow, Real.log_pow]
          norm_num only [Nat.cast_ofNat]
          linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
        have hu := Real.log_le_log (zero_lt_one.trans_le hy1) h400
        exact
          logQuadraticRemainder_pos_of_rectangle (by linarith only [h200] : (200 : ℝ) ≤ y) hz0
            (by linarith only [hd.1] : (24 / 5 : ℝ) ≤ Real.log y) (hu.trans hlog400.le)
            (by norm_num only)
      · by_cases h1024 : y ≤ 1024
        · have hd :=
            log_dyadic_bounds (a := 8) (b := 10)
              (by
                norm_num only; linarith only [h400] : (2 : ℝ) ^ 8 ≤ y)
              (by
                norm_num only; exact h1024 : y ≤ (2 : ℝ) ^ 10)
          norm_num only [Nat.cast_ofNat] at hd
          exact
            logQuadraticRemainder_pos_of_rectangle (by linarith only [h400] : (400 : ℝ) ≤ y) hz0
              (by linarith only [hd.1] : (11 / 2 : ℝ) ≤ Real.log y)
              (by linarith only [hd.2] : Real.log y ≤ (7 : ℝ)) (by norm_num only)
        · have hs := log_sq_le_sixteenth_of_1024 (by linarith only [h1024])
          linarith only [hs, hz0, hy]

end PseudoPrime.Analysis
