/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FinerPart2CutoffBounds
public import PseudoPrime.Analysis.Below64MainErrorBounds

/-! # Part 2 separation from height seven and cutoff fifty -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a root at least seven, a reciprocal loss at least 3/2, and the coupled level bounds.
Claim: the reciprocal bound, log upper bound with error -5/2, and Riemann lower bound conflict.
Proof: clear positive denominators and retain the positive remainder polynomials from height seven.
Role: extend the analytic Part 2 separation to cutoff fifty. -/
theorem refinedPart2_bounds_incompatible_of_root_ge_seven {t z L F R S b r : ℝ} (ht : (7 : ℝ) ≤ t)
    (hz : 0 ≤ z) (hrcost : (3 / 2 : ℝ) ≤ r)
    (hL : (t - 2) * L ≤ (t - 2) * t + t * (2 * z - (2 * r + 701 / 500))) (hzupper : z ≤ t / 3)
    (hF : F ≤ L - 2096 / 1831) (hR : 2 * z - r ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * z) * b + F * z - 5 / 2)
    (hl : t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (42781 / 915500 : ℝ) * (t + 1) ≤ S) : False := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 7) ht
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
        (5 / 2 : ℝ) * (t - 2) * (t - 1) ^ 2 := by
    nlinarith only [hmu3, hmb3, hmf3, hml]
  have hid :
    (t ^ 2 - (1839 / 500 : ℝ) * z - 1 - (42781 / 915500 : ℝ) * (t + 1)) * (t - 2) * (t - 1) ^ 2 -
        (((t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2) *
              ((t - 2) * t + t * (2 * z - (2 * r + 701 / 500)) - (2096 / 1831 : ℝ) * (t - 2)) +
            (t - 2) * (2 * t + 2 + 2 * z) * (r - 1 / 4 - 2 * z) * t ^ 2 -
          (5 / 2 : ℝ) * (t - 2) * (t - 1) ^ 2) =
      ((14325249 / 915500 : ℝ) - 1 / 4) * t ^ 3 - ((2948578 / 228875 : ℝ) - 1) * t ^ 2 +
                ((3069251 / 915500 : ℝ) - 5 / 4) * t -
              255672 / 228875 +
            1 / 2 +
            z *
              ((4500103 / 915500 : ℝ) * t ^ 3 - (2728363 / 457750 : ℝ) * t ^ 2 -
                  (2162609 / 183100 : ℝ) * t +
                1839 / 250) -
          4 * t ^ 2 * z ^ 2 +
        (r - 3 / 2) * (2 * t * (t ^ 2 * z + 2 * t ^ 2 + t - 1)) := by
    ring
  have ht3 : (7 : ℝ) * t ^ 2 ≤ t ^ 3 := by
    have h := mul_le_mul_of_nonneg_right ht (sq_nonneg t)
    nlinarith only [h]
  have hbase :
    0 <
      ((14325249 / 915500 : ℝ) - 1 / 4) * t ^ 3 - ((2948578 / 228875 : ℝ) - 1) * t ^ 2 +
            ((3069251 / 915500 : ℝ) - 5 / 4) * t -
          255672 / 228875 +
        1 / 2 := by
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
      ((14325249 / 915500 : ℝ) - 1 / 4) * t ^ 3 - ((2948578 / 228875 : ℝ) - 1) * t ^ 2 +
                ((3069251 / 915500 : ℝ) - 5 / 4) * t -
              255672 / 228875 +
            1 / 2 +
            z *
              ((4500103 / 915500 : ℝ) * t ^ 3 - (2728363 / 457750 : ℝ) * t ^ 2 -
                  (2162609 / 183100 : ℝ) * t +
                1839 / 250) -
          4 * t ^ 2 * z ^ 2 +
        (r - 3 / 2) * (2 * t * (t ^ 2 * z + 2 * t ^ 2 + t - 1)) := by
    nlinarith only [hbase, hzzmul, hzcoeff, hQ]
  have hms := mul_le_mul_of_nonneg_right hl (mul_nonneg htp.le (sq_nonneg (t - 1)))
  nlinarith only [hms, hu2, hid, hp]

/-- Input: a real cutoff at least fifty. Claim: the odd log main error is at most -5/2.
Proof: certify the logarithm of fifty and keep the Euler lower bound.
Role: supply the odd branch of the larger low-scale analytic range. -/
theorem primitiveLogOddMainError_le_five_halves_of_ge_fifty {x : ℝ} (hx : 50 ≤ x) :
    primitiveLogOddMainError x ≤ -(5 / 2 : ℝ) := by
  have hc : rationalLogIntervalCheck 50 6 10 (39 / 10) 4 = true := by decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 50) hx
  have hlog : (39 / 10 : ℝ) ≤ Real.log x := hl.trans hm
  have hcoef : (1961 / 2000 : ℝ) ≤ Real.log 2 + Real.eulerMascheroniConstant / 2 := by
    linarith only [Real.log_two_gt_d9, twentyThree_fortieths_lt_eulerMascheroniConstant]
  have hp :=
    mul_le_mul hcoef hlog (by norm_num only : (0 : ℝ) ≤ 39 / 10) (le_trans (by norm_num only) hcoef)
  unfold primitiveLogOddMainError
  nlinarith only [hp, Real.pi_lt_d4, Real.pi_pos]

/-- Input: a real cutoff at least fifty. Claim: the even log main error is at most -5/2.
Proof: retain the negative quadratic logarithmic term.
Role: supply the even branch of the larger low-scale analytic range. -/
theorem primitiveLogEvenMainError_le_five_halves_of_ge_fifty {x : ℝ} (hx : 50 ≤ x) :
    primitiveLogEvenMainError x ≤ -(5 / 2 : ℝ) := by
  have hc : rationalLogIntervalCheck 50 6 10 (39 / 10) 4 = true := by decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have hlog := hl.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 50) hx)
  have hprod :=
    mul_le_mul_of_nonneg_right Real.one_half_lt_eulerMascheroniConstant.le
      (le_trans (by norm_num only) hlog)
  unfold primitiveLogEvenMainError
  nlinarith only [hprod, hlog, Real.pi_lt_four, Real.pi_pos]

/-- Input: a logarithmic level at least 6.21.
Claim: the finer root is at least seven and its square is at least fifty.
Proof: certify the tangent point and apply the logarithm tangent on the entire half-line.
Role: discharge the revised comparison's height and cutoff inputs. -/
theorem finerPart2Root_height_and_cutoff_of_ge_621_div_100 {L : ℝ} (hL : (621 / 100 : ℝ) ≤ L) :
    7 ≤ finerPart2CutoffRoot L ∧ 50 ≤ (finerPart2CutoffRoot L) ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc : rationalLogIntervalCheck (621 / 100) 3 10 (182 / 100) (183 / 100) = true := by
    decide +kernel
  have hh := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hh
  have ht := log_le_log_add_sub_div (a := (621 / 100 : ℝ)) (y := L) (by norm_num only) hL0
  have hb : (71071 / 10000 : ℝ) ≤ finerPart2CutoffRoot L := by
    dsimp only [finerPart2CutoffRoot]
    linarith only [ht, hh, hL]
  constructor
  · linarith only [hb]
  · nlinarith only [hb]

/-- Input: a modulus at least 501. Claim: its logarithm is at least 6.21.
Proof: certify log 501 and apply logarithm monotonicity.
Role: supply the analytic high branch without modulus enumeration. -/
theorem log_level_ge_seven_root_entrance {q : ℕ} (hq : 501 ≤ q) : (621 / 100 : ℝ) ≤ Real.log q := by
  have hc : rationalLogIntervalCheck 501 9 10 (621 / 100) (622 / 100) = true := by decide +kernel
  have h := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hq))

end PseudoPrime.Analysis
