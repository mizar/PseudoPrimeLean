/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPart2CutoffBounds

/-! # Sharper Part 2 cutoff from the existing precise constants -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The sharper Part 2 root L-2 log L+2301/500.
Its square is the cutoff for the rational triple (1,-2,2301/500).
This numerical definition is shared by LLS and its prime-test consumers. -/
noncomputable def sharperPart2CutoffRoot (L : ℝ) : ℝ :=
  L - 2 * Real.log L + 2301 / 500

/-- For L ≥ 8, the sharper Part 2 root exceeds eight.
Use a logarithm tangent at eight and the certified logarithm of two.
This places the squared cutoff in the analytic range x ≥ 64. -/
theorem eight_lt_sharperPart2CutoffRoot {L : ℝ} (hL : 8 ≤ L) : 8 < sharperPart2CutoffRoot L := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := log_le_log_add_sub_div (a := (8 : ℝ)) (y := L) (by norm_num only) hL0
  have h8 : Real.log (8 : ℝ) ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  unfold sharperPart2CutoffRoot
  linarith only [ht, h8, hL]

/-- For positive L,t and t=L-2log L+c, the logarithm tangent gives the
displayed coupled level bound. The correction c is arbitrary. This generic
interface supports sharper Part 2 constants without repeating the algebra. -/
theorem logarithmicCutoffRoot_coupled_level_bound {L t c : ℝ} (hL : 0 < L) (ht : 0 < t)
    (he : t = L - 2 * Real.log L + c) : (t - 2) * L ≤ (t - 2) * t + t * (2 * Real.log t - c) := by
  have hlog := log_le_log_add_sub_div (a := t) (y := L) ht hL
  have hm := mul_le_mul_of_nonneg_right hlog ht.le
  rw [add_mul, div_mul_cancel₀ _ ht.ne'] at hm
  have hemul := congrArg (fun u : ℝ ↦ u * t) he
  nlinarith only [hm, hemul]

/-- For L ≥ 8, the sharper root satisfies the coupled level bound with
constant 2301/500. Apply the generic positive-root tangent identity.
The dependence on the actual logarithmic level is retained in the separation. -/
theorem sharperPart2CutoffRoot_coupled_level_bound {L : ℝ} (hL : 8 ≤ L) :
    let t := sharperPart2CutoffRoot L;
    (t - 2) * L ≤ (t - 2) * t + t * (2 * Real.log t - 2301 / 500) := by
  exact
    logarithmicCutoffRoot_coupled_level_bound (by linarith only [hL])
      ((by norm_num only : (0 : ℝ) < 8).trans (eight_lt_sharperPart2CutoffRoot hL)) rfl

/-- If r is at least 3/2, the reciprocal lower bound log(x)-r yields
a contradiction with additive correction 2*r+701/500 under the displayed inputs.
Retain the loss parameter through the exact polynomial separation.
Its dependence is a nonnegative correction to the base case r=3/2.
This permits sharper Riemann reciprocal estimates without repeating the proof. -/
theorem refinedPart2_bounds_incompatible_of_reciprocal_cost {t z L F R S b r : ℝ}
    (ht : (15 / 2 : ℝ) < t) (hz : 0 ≤ z) (hrcost : (3 / 2 : ℝ) ≤ r)
    (hL : (t - 2) * L ≤ (t - 2) * t + t * (2 * z - (2 * r + 701 / 500))) (hzupper : z ≤ t / 3)
    (hF : F ≤ L - 2096 / 1831) (hR : 2 * z - r ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * z) * b + F * z - 11 / 4)
    (hl : t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (42781 / 915500 : ℝ) * (t + 1) ≤ S) : False := by
  have ht0 : 0 < t := lt_trans (by norm_num only : (0 : ℝ) < 15 / 2) ht
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg t)
  have he1 : t ^ 2 * ((1 - 1 / t) ^ 2 * b) = (t - 1) ^ 2 * b := by
    have he : t * (1 - 1 / t) = t - 1 := by
      have hc := div_mul_cancel₀ (1 : ℝ) ht0.ne'
      nlinarith only [hc]
    calc
      _ = (t * (1 - 1 / t)) ^ 2 * b := by ring
      _ = _ := by rw [he]
  have he2 :
    t ^ 2 * ((1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4) =
      (1 / 2 : ℝ) * (t ^ 2 - 1) * F - R * t ^ 2 - t ^ 2 / 4 := by
    have hc := div_mul_cancel₀ (1 : ℝ) (sq_pos_of_pos ht0).ne'
    have hm := congrArg (fun v : ℝ ↦ v * F) hc
    nlinarith only [hm]
  rw [he1, he2] at hm
  have hr := mul_le_mul_of_nonneg_right hR (sq_nonneg t)
  have hb2 : (t - 1) ^ 2 * b ≤ (1 / 2 : ℝ) * (t ^ 2 - 1) * F + (r - 1 / 4 - 2 * z) * t ^ 2 := by
    nlinarith only [hm, hr]
  have hC : 0 ≤ 2 * t + 2 + 2 * z := by linarith only [ht, hz]
  have hcoef : 0 ≤ (t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2 :=
    add_nonneg (mul_nonneg (by linarith only [ht, hz]) (by nlinarith only [ht]))
      (mul_nonneg hz (sq_nonneg _))
  have hmu := mul_le_mul_of_nonneg_left hu (sq_nonneg (t - 1))
  have hmb := mul_le_mul_of_nonneg_left hb2 hC
  have hmf := mul_le_mul_of_nonneg_left hF hcoef
  have htp : 0 < t - 2 := by linarith only [ht]
  have hml := mul_le_mul_of_nonneg_left hL hcoef
  have hmu3 := mul_le_mul_of_nonneg_left hmu htp.le
  have hmb3 := mul_le_mul_of_nonneg_left hmb htp.le
  have hmf3 := mul_le_mul_of_nonneg_left hmf htp.le
  have hu2 :
    (t - 2) * (t - 1) ^ 2 * S ≤
      ((t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2) *
            ((t - 2) * t + t * (2 * z - (2 * r + 701 / 500)) - (2096 / 1831 : ℝ) * (t - 2)) +
          (t - 2) * (2 * t + 2 + 2 * z) * (r - 1 / 4 - 2 * z) * t ^ 2 -
        (11 / 4 : ℝ) * (t - 2) * (t - 1) ^ 2 := by
    nlinarith only [hmu3, hmb3, hmf3, hml]
  have hid :
    (t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (42781 / 915500 : ℝ) * (t + 1)) * (t - 2) * (t - 1) ^ 2 -
        (((t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2) *
              ((t - 2) * t + t * (2 * z - (2 * r + 701 / 500)) - (2096 / 1831 : ℝ) * (t - 2)) +
            (t - 2) * (2 * t + 2 + 2 * z) * (r - 1 / 4 - 2 * z) * t ^ 2 -
          (11 / 4 : ℝ) * (t - 2) * (t - 1) ^ 2) =
      (14325249 / 915500 : ℝ) * t ^ 3 - (2948578 / 228875 : ℝ) * t ^ 2 +
                (3069251 / 915500 : ℝ) * t -
              255672 / 228875 +
            z *
              ((4500103 / 915500 : ℝ) * t ^ 3 - (2728363 / 457750 : ℝ) * t ^ 2 -
                  (2162609 / 183100 : ℝ) * t +
                1839 / 250) -
          4 * t ^ 2 * z ^ 2 +
        (r - 3 / 2) * (2 * t * (t ^ 2 * z + 2 * t ^ 2 + t - 1)) := by
    ring
  have ht3 : (15 / 2 : ℝ) * t ^ 2 < t ^ 3 := by
    have h := mul_lt_mul_of_pos_right ht (sq_pos_of_pos ht0)
    nlinarith only [h]
  have hbase :
    0 <
      (14325249 / 915500 : ℝ) * t ^ 3 - (2948578 / 228875 : ℝ) * t ^ 2 +
          (3069251 / 915500 : ℝ) * t -
        255672 / 228875 := by
    nlinarith only [ht3, sq_nonneg (t - 1), ht]
  have hcoeff :
    0 ≤
      (9838309 / 2746500 : ℝ) * t ^ 3 - (2728363 / 457750 : ℝ) * t ^ 2 -
          (2162609 / 183100 : ℝ) * t +
        1839 / 250 := by
    nlinarith only [ht3, sq_nonneg (t - 1), ht]
  have hzz := mul_nonneg hz (sub_nonneg.mpr hzupper)
  have hzzmul := mul_nonneg (sq_nonneg t) hzz
  have hzcoeff := mul_nonneg hz hcoeff
  have hQ : 0 ≤ (r - 3 / 2) * (2 * t * (t ^ 2 * z + 2 * t ^ 2 + t - 1)) :=
    mul_nonneg (sub_nonneg.mpr hrcost)
      (mul_nonneg (by linarith only [ht] : 0 ≤ 2 * t)
        (by nlinarith only [mul_nonneg (sq_nonneg t) hz, sq_nonneg t, ht]))
  have hp :
    0 <
      (14325249 / 915500 : ℝ) * t ^ 3 - (2948578 / 228875 : ℝ) * t ^ 2 +
                (3069251 / 915500 : ℝ) * t -
              255672 / 228875 +
            z *
              ((4500103 / 915500 : ℝ) * t ^ 3 - (2728363 / 457750 : ℝ) * t ^ 2 -
                  (2162609 / 183100 : ℝ) * t +
                1839 / 250) -
          4 * t ^ 2 * z ^ 2 +
        (r - 3 / 2) * (2 * t * (t ^ 2 * z + 2 * t ^ 2 + t - 1)) := by
    nlinarith only [hbase, hzzmul, hzcoeff, hQ]
  have hms := mul_le_mul_of_nonneg_right hl (mul_nonneg htp.le (sq_nonneg (t - 1)))
  nlinarith only [hms, hu2, hid, hp]

/-- For t greater than 15/2, 0 ≤ z ≤ t/3 and the displayed coupled level
condition, the raw reciprocal and logarithmic bounds are incompatible.
The exact polynomial separation remains positive below height eight.
This generic comparison permits numerical cutoffs below 64. -/
theorem refinedPart2_bounds_incompatible_of_root_gt_fifteen_halves {t z L F R S b : ℝ}
    (ht : (15 / 2 : ℝ) < t) (hz : 0 ≤ z) (hL : (t - 2) * L ≤ (t - 2) * t + t * (2 * z - 2301 / 500))
    (hzupper : z ≤ t / 3) (hF : F ≤ L - 2096 / 1831) (hR : 2 * z - 8 / 5 ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * z) * b + F * z - 11 / 4)
    (hl : t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (42781 / 915500 : ℝ) * (t + 1) ≤ S) : False := by
  apply
    refinedPart2_bounds_incompatible_of_reciprocal_cost ht hz
      (by norm_num only : (3 / 2 : ℝ) ≤ 8 / 5) ?_ hzupper hF hR hb hu hl
  nlinarith only [hL]

/-- For t > 8 and 0 ≤ z ≤ t/3, the raw reciprocal and logarithmic upper
bounds contradict the Riemann lower bound when the coupled level condition holds.
Clear the reciprocal denominator explicitly and multiply the level condition by t-2.
The sharpened zero-mass and log pi constants give positive remaining polynomials.
This proves the smaller rational Part 2 correction on the entire half-line. -/
theorem refinedPart2_bounds_incompatible_2301_div_500 {t z L F R S b : ℝ} (ht : 8 < t) (hz : 0 ≤ z)
    (hL : (t - 2) * L ≤ (t - 2) * t + t * (2 * z - 2301 / 500)) (hzupper : z ≤ t / 3)
    (hF : F ≤ L - 2096 / 1831) (hR : 2 * z - 8 / 5 ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * z) * b + F * z - 11 / 4)
    (hl : t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (42781 / 915500 : ℝ) * (t + 1) ≤ S) : False := by
  exact
    refinedPart2_bounds_incompatible_of_root_gt_fifteen_halves
      (lt_trans (by norm_num only : (15 / 2 : ℝ) < 8) ht) hz hL hzupper hF hR hb hu hl

end PseudoPrime.Analysis
