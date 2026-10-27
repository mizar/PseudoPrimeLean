/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogarithmicCutoffBounds
public import PseudoPrime.Analysis.LogarithmicShiftBounds
public import PseudoPrime.Analysis.RefinedPart2Separation

/-! # Rational Part 2 cutoff with constant 193/40 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational Part 2 root L-2 log L+193/40.
Its square is the cutoff for the rational triple (1,-2,193/40).
This numerical definition is shared by LLS and its prime-test consumers. -/
noncomputable def rationalPart2CutoffRoot (L : ℝ) : ℝ :=
  L - 2 * Real.log L + 193 / 40

/-- For L ≥ 8, the rational Part 2 root exceeds eight.
Use a logarithm tangent at eight and the certified logarithm of two.
This places the squared cutoff in the analytic range x ≥ 64. -/
theorem eight_lt_rationalPart2CutoffRoot {L : ℝ} (hL : 8 ≤ L) : 8 < rationalPart2CutoffRoot L := by
  have hL0 : 0 < L := by linarith only [hL]
  have ht := log_le_log_add_sub_div (a := (8 : ℝ)) (y := L) (by norm_num only) hL0
  have h8 : Real.log (8 : ℝ) ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  unfold rationalPart2CutoffRoot
  linarith only [ht, h8, hL]

/-- For t ≥ 8, log t ≤ t/3. Apply a logarithm tangent at eight
and absorb the constant at the endpoint. This controls the quadratic logarithmic term. -/
theorem log_le_third_of_ge_eight {t : ℝ} (ht : 8 ≤ t) : Real.log t ≤ t / 3 := by
  have ht0 : 0 < t := by linarith only [ht]
  have hlog := log_le_log_add_sub_div (a := (8 : ℝ)) (y := t) (by norm_num only) ht0
  have h8 : Real.log (8 : ℝ) ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  linarith only [hlog, h8, ht]

/-- For L ≥ 8, the rational root t satisfies the displayed coupled level bound.
Retain the tangent denominator rather than replacing it by a fixed ratio allowance.
This preserves the rational constant 193/40 in the weighted comparison. -/
theorem rationalPart2CutoffRoot_coupled_level_bound {L : ℝ} (hL : 8 ≤ L) :
    let t := rationalPart2CutoffRoot L;
    (t - 2) * L ≤ (t - 2) * t + t * (2 * Real.log t - 193 / 40) := by
  let t := rationalPart2CutoffRoot L
  have hL0 : 0 < L := by linarith only [hL]
  have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 8).trans (eight_lt_rationalPart2CutoffRoot hL)
  have ht := log_le_log_add_sub_div (a := t) (y := L) ht0 hL0
  have hm := mul_le_mul_of_nonneg_right ht ht0.le
  rw [add_mul, div_mul_cancel₀ _ ht0.ne'] at hm
  have he : L = t + 2 * Real.log L - 193 / 40 := by
    dsimp only [t, rationalPart2CutoffRoot]
    ring
  have hemul := congrArg (fun u : ℝ ↦ u * t) he
  change (t - 2) * L ≤ (t - 2) * t + t * (2 * Real.log t - 193 / 40)
  nlinarith only [hm, hemul]

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- For t > 8 and 0 ≤ z ≤ t/3, the raw reciprocal and logarithmic upper
bounds contradict the Riemann lower bound when the coupled level condition holds.
Clear the reciprocal denominator explicitly and multiply the level condition by t-2.
The leading polynomial coefficient vanishes at 193/40; the remaining terms are positive.
This proves the smaller rational Part 2 correction on the entire half-line. -/
theorem refinedPart2_bounds_incompatible_193_div_40 {t z L F R S b : ℝ} (ht : 8 < t) (hz : 0 ≤ z)
    (hL : (t - 2) * L ≤ (t - 2) * t + t * (2 * z - 193 / 40)) (hzupper : z ≤ t / 3) (hF : F ≤ L - 1)
    (hR : 2 * z - 8 / 5 ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * z) * b + F * z - 11 / 4)
    (hl : t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (t + 1) / 8 ≤ S) : False := by
  have ht0 : 0 < t := lt_trans (by norm_num only : (0 : ℝ) < 8) ht
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
  have hb2 : (t - 1) ^ 2 * b ≤ (1 / 2 : ℝ) * (t ^ 2 - 1) * F + (27 / 20 - 2 * z) * t ^ 2 := by
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
            ((t - 2) * t + t * (2 * z - 193 / 40) - (t - 2)) +
          (t - 2) * (2 * t + 2 + 2 * z) * (27 / 20 - 2 * z) * t ^ 2 -
        (11 / 4 : ℝ) * (t - 2) * (t - 1) ^ 2 := by
    nlinarith only [hmu3, hmb3, hmf3, hml]
  have hid :
    (t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (t + 1) / 8) * (t - 2) * (t - 1) ^ 2 -
        (((t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2) *
              ((t - 2) * t + t * (2 * z - 193 / 40) - (t - 2)) +
            (t - 2) * (2 * t + 2 + 2 * z) * (27 / 20 - 2 * z) * t ^ 2 -
          (11 / 4 : ℝ) * (t - 2) * (t - 1) ^ 2) =
      (333 / 20 : ℝ) * t ^ 3 - (251 / 20 : ℝ) * t ^ 2 + (51 / 20 : ℝ) * t - 5 / 4 +
          z *
            ((659 / 125 : ℝ) * t ^ 3 - (2769 / 500 : ℝ) * t ^ 2 - (1239 / 100 : ℝ) * t +
              1839 / 250) -
        4 * t ^ 2 * z ^ 2 := by
    ring
  have ht3 : 8 * t ^ 2 < t ^ 3 := by
    have h := mul_lt_mul_of_pos_right ht (sq_pos_of_pos ht0)
    nlinarith only [h]
  have hbase : 0 < (333 / 20 : ℝ) * t ^ 3 - (251 / 20 : ℝ) * t ^ 2 + (51 / 20 : ℝ) * t - 5 / 4 := by
    nlinarith only [ht3, sq_nonneg (t - 1), ht]
  have hcoeff :
    0 ≤
      (1477 / 375 : ℝ) * t ^ 3 - (2769 / 500 : ℝ) * t ^ 2 - (1239 / 100 : ℝ) * t + 1839 / 250 := by
    nlinarith only [ht3, sq_nonneg (t - 1), ht]
  have hzz := mul_nonneg hz (sub_nonneg.mpr hzupper)
  have hzzmul := mul_nonneg (sq_nonneg t) hzz
  have hzcoeff := mul_nonneg hz hcoeff
  have hp :
    0 <
      (333 / 20 : ℝ) * t ^ 3 - (251 / 20 : ℝ) * t ^ 2 + (51 / 20 : ℝ) * t - 5 / 4 +
          z *
            ((659 / 125 : ℝ) * t ^ 3 - (2769 / 500 : ℝ) * t ^ 2 - (1239 / 100 : ℝ) * t +
              1839 / 250) -
        4 * t ^ 2 * z ^ 2 := by
    nlinarith only [hbase, hzzmul, hzcoeff]
  have hms := mul_le_mul_of_nonneg_right hl (mul_nonneg htp.le (sq_nonneg (t - 1)))
  nlinarith only [hms, hu2, hid, hp]

end PseudoPrime.Analysis
