/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Tactic

/-! # Polynomial separation for the refined Part 2 cutoff -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For t>8 and z≥0, the reciprocal and logarithmic raw bounds are incompatible
with the Riemann lower bound when L≤t+2z−73/15 and the conductor term F≤L−1.
Clear the reciprocal denominator and bound the affine coefficient of L.
The remaining gap is a polynomial with positive cubic term and nonnegative lower terms.
This closes the numerical comparison at t=L−2log(L)+5 without changing the analytic core. -/
theorem refinedPart2_bounds_incompatible {t z L F R S b : ℝ} (ht : 8 < t) (hz : 0 ≤ z)
    (hL : L ≤ t + 2 * z - 73 / 15) (hF : F ≤ L - 1) (hR : 2 * z - 8 / 5 ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * z) * b + F * z - 11 / 4)
    (hl : t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (t + 1) / 8 ≤ S) : False := by
  have ht0 : 0 < t := lt_trans (by norm_num only : (0 : ℝ) < 8) ht
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg t)
  have he1 : t ^ 2 * ((1 - 1 / t) ^ 2 * b) = (t - 1) ^ 2 * b := by field_simp [ht0.ne']
  have he2 :
    t ^ 2 * ((1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4) =
      (1 / 2 : ℝ) * (t ^ 2 - 1) * F - R * t ^ 2 - t ^ 2 / 4 := by
    field_simp [ht0.ne']
  rw [he1, he2] at hm
  have hr := mul_le_mul_of_nonneg_right hR (sq_nonneg t)
  have hb2 : (t - 1) ^ 2 * b ≤ (1 / 2 : ℝ) * (t ^ 2 - 1) * F + (27 / 20 - 2 * z) * t ^ 2 := by
    nlinarith only [hm, hr]
  have hC : 0 ≤ 2 * t + 2 + 2 * z := by linarith only [ht, hz]
  have hcoef : 0 ≤ (t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2 :=
    add_nonneg (mul_nonneg (by linarith only [ht, hz]) (by nlinarith only [ht]))
      (mul_nonneg hz (sq_nonneg _))
  have hmu := mul_le_mul_of_nonneg_left hu (sq_nonneg (t - 1))
  have hmb := mul_le_mul_of_nonneg_left hb2 hC
  have hmf := mul_le_mul_of_nonneg_left hF hcoef
  have hml := mul_le_mul_of_nonneg_left hL hcoef
  have hu2 :
    (t - 1) ^ 2 * S ≤
      ((t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2) * (t + 2 * z - 73 / 15 - 1) +
          (2 * t + 2 + 2 * z) * (27 / 20 - 2 * z) * t ^ 2 -
        (11 / 4 : ℝ) * (t - 1) ^ 2 := by
    nlinarith only [hmu, hmb, hmf, hml]
  have hid :
    (t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (t + 1) / 8) * (t - 1) ^ 2 -
        (((t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2) * (t + 2 * z - 73 / 15 - 1) +
            (2 * t + 2 + 2 * z) * (27 / 20 - 2 * z) * t ^ 2 -
          (11 / 4 : ℝ) * (t - 1) ^ 2) =
      t ^ 3 / 24 + (845 * t ^ 2 - 989 * t - 509) / 120 +
        z * (14033 * t ^ 2 - 3566 * t - 2517) / 1500 +
        4 * t * z ^ 2 := by
    ring
  have ha : 0 < 845 * t ^ 2 - 989 * t - 509 := by nlinarith only [sq_nonneg (t - 1), ht]
  have hc : 0 ≤ 14033 * t ^ 2 - 3566 * t - 2517 := by nlinarith only [sq_nonneg (t - 1), ht]
  have hp :
    0 <
      t ^ 3 / 24 + (845 * t ^ 2 - 989 * t - 509) / 120 +
        z * (14033 * t ^ 2 - 3566 * t - 2517) / 1500 +
        4 * t * z ^ 2 := by
    have h1 := pow_pos ht0 3
    have h2 := mul_nonneg hz hc
    have h3 := mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) ht0.le) (sq_nonneg z)
    linarith only [h1, ha, h2, h3]
  have hms := mul_le_mul_of_nonneg_right hl (sq_nonneg (t - 1))
  nlinarith only [hms, hu2, hid, hp]

end PseudoPrime.Analysis
