/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneHalfShiftSeparation

/-! # Logarithm-dependent root savings on an unbounded analytic interval -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The gap for allowance log(y)-2 is the half-shift gap minus the exact
additional conductor cost. Input z represents log y. Its positivity yields
an increasing saving rather than a fixed root correction. -/
noncomputable def qNeOneLogShiftGap (y z : ℝ) : ℝ :=
  qNeOneHalfShiftGap y z - (z - 5 / 2) * ((2 * y + 2 + 2 * z) * (y ^ 2 - 1) / 2 + z * (y - 1) ^ 2)

/-- Above root twelve and logarithm argument two, the gap increases in z.
Factor its difference and certify the coefficient. This allows reuse of the
rational logarithm minorant from the half-shift comparison. -/
theorem qNeOneLogShiftGap_mono {y z a : ℝ} (hy : (12 : ℝ) ≤ y) (ha : 2 ≤ a) (hz : a ≤ z) :
    qNeOneLogShiftGap y a ≤ qNeOneLogShiftGap y z := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hp := mul_nonneg (sq_nonneg y) (show 0 ≤ z + a by linarith only [ha, hz])
  have hq := mul_nonneg hy0 (show 0 ≤ z + a by linarith only [ha, hz])
  have hc :
    0 ≤
      y ^ 3 + 2 * y ^ 2 * (z + a) + 2 * y * (z + a) + (2659 / 1000 : ℝ) * y ^ 2 +
          (369 / 100 : ℝ) * y -
        2103 / 1000 := by
    nlinarith only [pow_nonneg hy0 3, sq_nonneg y, hp, hq, hy]
  have he :
    qNeOneLogShiftGap y z - qNeOneLogShiftGap y a =
      (z - a) *
        (y ^ 3 + 2 * y ^ 2 * (z + a) + 2 * y * (z + a) + (2659 / 1000 : ℝ) * y ^ 2 +
            (369 / 100 : ℝ) * y -
          2103 / 1000) := by
    unfold qNeOneLogShiftGap qNeOneHalfShiftGap qNeOneDeciShiftGap qNeOneRetainedGap
    ring
  exact sub_nonneg.mp (he ▸ mul_nonneg (sub_nonneg.mpr hz) hc)

/-- Above twelve, the gap at the rational logarithm minorant is positive.
Clear its denominator and shift by twelve; all six coefficients are positive.
This certifies the entire half-line without interval subdivision. -/
theorem qNeOneLogShiftGap_rational_pos {y : ℝ} (hy : (12 : ℝ) ≤ y) :
    0 < qNeOneLogShiftGap y (qNeOneHalfShiftLogLower y) := by
  have hv : 0 ≤ y - 12 := sub_nonneg.mpr hy
  have hsum : 0 < y + 12 := by linarith only [hy]
  have he :
    (y + 12) ^ 2 * qNeOneLogShiftGap y (qNeOneHalfShiftLogLower y) =
      (2207 / 5000 : ℝ) * (y - 12) ^ 5 + (30635251 / 750000 : ℝ) * (y - 12) ^ 4 +
        (105505097 / 93750 : ℝ) * (y - 12) ^ 3 +
        (10059033373 / 750000 : ℝ) * (y - 12) ^ 2 +
        (1136237839 / 15625 : ℝ) * (y - 12) +
        2315418636 / 15625 := by
    unfold qNeOneLogShiftGap qNeOneHalfShiftGap qNeOneDeciShiftGap qNeOneRetainedGap
      qNeOneHalfShiftLogLower
    field_simp [hsum.ne']
    ring
  have hp : 0 < (y + 12) ^ 2 * qNeOneLogShiftGap y (qNeOneHalfShiftLogLower y) := by
    nlinarith only [he, pow_nonneg hv 5, pow_nonneg hv 4, pow_nonneg hv 3, sq_nonneg (y - 12), hv]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hsum)).mp hp

/-- For every y>=12 the actual logarithm gives a positive gap.
Combine rational positivity and logarithm monotonicity.
This supplies the variable conductor-saving separation. -/
theorem qNeOneLogShiftGap_pos {y : ℝ} (hy : (12 : ℝ) ≤ y) :
    0 < qNeOneLogShiftGap y (Real.log y) := by
  have hn : 0 ≤ 2 * (y - 12) / (y + 12) :=
    div_nonneg (mul_nonneg (by norm_num only) (sub_nonneg.mpr hy)) (by linarith only [hy])
  have ha : (2 : ℝ) ≤ qNeOneHalfShiftLogLower y := by
    unfold qNeOneHalfShiftLogLower
    linarith only [hn]
  exact
    (qNeOneLogShiftGap_rational_pos hy).trans_le
      (qNeOneLogShiftGap_mono hy ha (qNeOneHalfShift_log_lower hy))

/-- For y>=12 and L<=y+log y-2, the fixed reciprocal upper envelope is
below the Riemann lower envelope. Transport the old cap by its exact affine
conductor cost and apply positive gap. This supports logarithmic root savings. -/
theorem qNeOneLogShiftUpper_lt_lower {y L : ℝ} (hy : (12 : ℝ) ≤ y) (hL : L ≤ y + Real.log y - 2) :
    qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (1483 / 1000) (Real.log 2) <
      qNeOneReciprocalLower y := by
  have h8 : (8 : ℝ) ≤ y := by linarith only [hy]
  have hu :=
    qNeOneDeciShiftUpper_scaled_le h8
      (show L - (Real.log y - 21 / 10) ≤ y + 1 / 10 by linarith only [hL])
  have hs :=
    qNeOneReciprocalUpper_scaled_conductor_shift (f :=
      L - (Real.log y - 21 / 10) + Real.log 4 - Real.log Real.pi) (r := (1483 / 1000 : ℝ)) (d :=
      Real.log 2) (c := Real.log y - 21 / 10) h8
  have hf :
    L - (Real.log y - 21 / 10) + Real.log 4 - Real.log Real.pi + (Real.log y - 21 / 10) =
      L + Real.log 4 - Real.log Real.pi := by
    ring
  rw [hf] at hs
  have hid :
    (y - 1) ^ 2 * qNeOneReciprocalLower y - qNeOneDeciShiftUpperScaledCap y (Real.log y) -
        (Real.log y - 21 / 10) *
          ((2 * y + 2 + 2 * Real.log y) * (y ^ 2 - 1) / 2 + Real.log y * (y - 1) ^ 2) =
      qNeOneLogShiftGap y (Real.log y) := by
    unfold qNeOneReciprocalLower qNeOneDeciShiftUpperScaledCap qNeOneLogShiftGap qNeOneHalfShiftGap
      qNeOneDeciShiftGap qNeOneRetainedGap
    ring
  have hp := qNeOneLogShiftGap_pos hy
  by_contra h
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg (y - 1))
  nlinarith only [hu, hs, hid, hp, hm]

end PseudoPrime.LLS.Extensions
