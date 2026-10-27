/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPart2CutoffBounds

/-! # Separation for the Part 2 comparison at a strictly smaller logarithmic cutoff -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The cleared difference of the Part 2 lower and upper bounds at level `t + 1/1000`.
Inputs are the positive cutoff root `t` and its logarithm `z`.
Its positivity gives the scalar contradiction used by the arbitrary-cutoff character theorem. -/
noncomputable def subsquarePart2Polynomial (t z : ℝ) : ℝ :=
  2 * t ^ 3 * z - (2413 / 500 : ℝ) * t ^ 3 + 4 * t ^ 2 * z ^ 2 + (81 / 50 : ℝ) * t ^ 2 * z +
        (1087 / 500 : ℝ) * t ^ 2 +
        (2679 / 500 : ℝ) * t * z -
      (1687 / 500 : ℝ) * t -
      (1839 / 500 : ℝ) * z +
    313 / 500

/-- Input: `t ≥ 8` and `z ≥ a ≥ 2`.
Claim: the cleared difference at `a` is no larger than at `z`.
Proof: factor the increment and bound its positive coefficient.
This permits constant logarithm bounds on each of two real intervals. -/
theorem subsquarePart2Polynomial_mono {t z a : ℝ} (ht : 8 ≤ t) (ha : 2 ≤ a) (hz : a ≤ z) :
    subsquarePart2Polynomial t a ≤ subsquarePart2Polynomial t z := by
  have ht0 : 0 ≤ t := (by norm_num only : (0 : ℝ) ≤ 8).trans ht
  have hza : 0 ≤ z + a := by linarith only [ha, hz]
  have hp := mul_nonneg (sq_nonneg t) hza
  have hc :
    0 ≤
      2 * t ^ 3 + 4 * t ^ 2 * (z + a) + (81 / 50 : ℝ) * t ^ 2 + (2679 / 500 : ℝ) * t -
        1839 / 500 := by
    nlinarith only [pow_nonneg ht0 3, sq_nonneg t, hp, ht]
  have he :
    subsquarePart2Polynomial t z - subsquarePart2Polynomial t a =
      (z - a) *
        (2 * t ^ 3 + 4 * t ^ 2 * (z + a) + (81 / 50 : ℝ) * t ^ 2 + (2679 / 500 : ℝ) * t -
          1839 / 500) := by
    unfold subsquarePart2Polynomial
    ring
  exact sub_nonneg.mp (he ▸ mul_nonneg (sub_nonneg.mpr hz) hc)

/-- Input: `8 ≤ t ≤ 16`.
Claim: the cleared difference with logarithm lower bound two is positive.
Proof: absorb the negative cubic term into the positive quadratic term.
This covers the compact real interval without finite input enumeration. -/
theorem subsquarePart2Polynomial_pos_small {t : ℝ} (ht : 8 ≤ t) (hu : t ≤ 16) :
    0 < subsquarePart2Polynomial t 2 := by
  have hp := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hu)
  have he :
    subsquarePart2Polynomial t 2 =
      (4099 / 500 : ℝ) * t ^ 2 + (3671 / 500 : ℝ) * t - 673 / 100 +
        (413 / 500 : ℝ) * (t ^ 2 * (16 - t)) := by
    unfold subsquarePart2Polynomial
    ring
  nlinarith only [he, hp, sq_nonneg t, ht]

/-- Input: `t ≥ 16`.
Claim: the cleared difference with logarithm lower bound `5/2` is positive.
Proof: translate the variable by sixteen and use the positive coefficients.
This supplies the unbounded real interval. -/
theorem subsquarePart2Polynomial_pos_large {t : ℝ} (ht : 16 ≤ t) :
    0 < subsquarePart2Polynomial t (5 / 2) := by
  have hv : 0 ≤ t - 16 := sub_nonneg.mpr ht
  have he :
    subsquarePart2Polynomial t (5 / 2) =
      (87 / 500 : ℝ) * (t - 16) ^ 3 + (4947 / 125 : ℝ) * (t - 16) ^ 2 +
        (1142821 / 1000 : ℝ) * (t - 16) +
        1771563 / 200 := by
    unfold subsquarePart2Polynomial
    ring
  nlinarith only [he, pow_nonneg hv 3, sq_nonneg (t - 16), hv]

/-- Input: a real cutoff root at least eight.
Claim: the cleared Part 2 difference is strictly positive at its actual logarithm.
Proof: use the logarithm of eight below sixteen and the logarithm of sixteen above it.
This is the scale-independent scalar input to the character contradiction. -/
theorem subsquarePart2Polynomial_pos {t : ℝ} (ht : 8 ≤ t) :
    0 < subsquarePart2Polynomial t (Real.log t) := by
  have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9]
  have hlog16 : (5 / 2 : ℝ) ≤ Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9]
  by_cases hu : t ≤ 16
  · exact
      (subsquarePart2Polynomial_pos_small ht hu).trans_le
        (subsquarePart2Polynomial_mono ht (by norm_num only)
          (hlog8.trans (Real.log_le_log (by norm_num only) ht)))
  · exact
      (subsquarePart2Polynomial_pos_large (le_of_not_ge hu)).trans_le
        (subsquarePart2Polynomial_mono ht (by norm_num only)
          (hlog16.trans (Real.log_le_log (by norm_num only) (le_of_not_ge hu))))

/-- Input: a positive cutoff root, nonnegative logarithm, conductor bound and reciprocal estimate.
Claim: the logarithmic upper estimate has the displayed cleared affine bound.
Proof: clear reciprocal powers and multiply only by nonnegative coefficients.
The free conductor ceiling permits later cutoff choices without reproving the elimination. -/
theorem part2_cleared_upper_of_bounds {t z F F₀ R S b : ℝ} (ht : 1 < t) (hz : 0 ≤ z) (hF : F ≤ F₀)
    (hR : 2 * z - 8 / 5 ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * z) * b + F * z - 11 / 4) :
    (t - 1) ^ 2 * S ≤
      ((t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2) * F₀ +
          (2 * t + 2 + 2 * z) * (27 / 20 - 2 * z) * t ^ 2 -
        (11 / 4 : ℝ) * (t - 1) ^ 2 := by
  have ht0 : 0 < t := lt_trans (by norm_num only : (0 : ℝ) < 1) ht
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
    have hmul := congrArg (fun v : ℝ ↦ v * F) hc
    nlinarith only [hmul]
  rw [he1, he2] at hm
  have hr := mul_le_mul_of_nonneg_right hR (sq_nonneg t)
  have hb2 : (t - 1) ^ 2 * b ≤ (1 / 2 : ℝ) * (t ^ 2 - 1) * F + (27 / 20 - 2 * z) * t ^ 2 := by
    nlinarith only [hm, hr]
  have hC : 0 ≤ 2 * t + 2 + 2 * z := by linarith only [ht, hz]
  have hcoef : 0 ≤ (t + 1 + z) * (t ^ 2 - 1) + z * (t - 1) ^ 2 :=
    add_nonneg (mul_nonneg (by linarith only [ht, hz]) (by nlinarith only [ht]))
      (mul_nonneg hz (sq_nonneg (t - 1)))
  have hmu := mul_le_mul_of_nonneg_left hu (sq_nonneg (t - 1))
  have hmb := mul_le_mul_of_nonneg_left hb2 hC
  have hmf := mul_le_mul_of_nonneg_left hF hcoef
  nlinarith only [hmu, hmb, hmf]

/-- Input: the Part 2 estimates at a cutoff root at least eight and conductor ceiling t-999/1000.
Claim: those estimates contradict the Riemann lower bound.
Proof: the cleared difference is the strictly positive polynomial already certified above.
This supplies an analytic contradiction for every real cutoff in the stated range. -/
theorem subsquarePart2_bounds_incompatible {t F R S b : ℝ} (ht : 8 ≤ t) (hF : F ≤ t - 999 / 1000)
    (hR : 2 * Real.log t - 8 / 5 ≤ R)
    (hb : (1 - 1 / t) ^ 2 * b ≤ (1 / 2 : ℝ) * (1 - 1 / t ^ 2) * F - R - 1 / 4)
    (hu : S ≤ (2 * t + 2 + 2 * Real.log t) * b + F * Real.log t - 11 / 4)
    (hl : t ^ 2 - (1839 / 500 : ℝ) * Real.log t - 1 - (t + 1) / 8 ≤ S) : False := by
  have hz : 0 ≤ Real.log t := Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 8).trans ht)
  have hu' :=
    part2_cleared_upper_of_bounds ((by norm_num only : (1 : ℝ) < 8).trans_le ht) hz hF hR hb hu
  have hl' := mul_le_mul_of_nonneg_right hl (sq_nonneg (t - 1))
  have he :
    (t ^ 2 - (1839 / 500 : ℝ) * Real.log t - 1 - (t + 1) / 8) * (t - 1) ^ 2 -
        (((t + 1 + Real.log t) * (t ^ 2 - 1) + Real.log t * (t - 1) ^ 2) * (t - 999 / 1000) +
            (2 * t + 2 + 2 * Real.log t) * (27 / 20 - 2 * Real.log t) * t ^ 2 -
          (11 / 4 : ℝ) * (t - 1) ^ 2) =
      subsquarePart2Polynomial t (Real.log t) := by
    unfold subsquarePart2Polynomial
    ring
  have hp := subsquarePart2Polynomial_pos ht
  nlinarith only [hu', hl', he, hp]

end PseudoPrime.Analysis
