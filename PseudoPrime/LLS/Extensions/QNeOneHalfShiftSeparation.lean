/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneScaleReciprocalComparison

/-! # Whole-half-line comparison for a one-half root correction -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The one-half conductor allowance gap is the one-tenth gap minus its exact
additional two-fifths conductor cost. Inputs are root y and logarithm z.
Its positivity certifies the stronger reciprocal comparison. -/
noncomputable def qNeOneHalfShiftGap (y z : ℝ) : ℝ :=
  qNeOneDeciShiftGap y z - (2 / 5 : ℝ) * ((2 * y + 2 + 2 * z) * (y ^ 2 - 1) / 2 + z * (y - 1) ^ 2)

/-- The rational logarithm minorant anchored at twelve with value 621/250.
It is used above twelve to certify an unbounded interval without a grid. -/
noncomputable def qNeOneHalfShiftLogLower (y : ℝ) : ℝ :=
  621 / 250 + 2 * (y - 12) / (y + 12)

/-- For y>=12 and 2<=a<=z, the half-shift gap increases in z.
Factor the difference and certify its nonnegative coefficient.
This permits substitution of the rational logarithm minorant. -/
theorem qNeOneHalfShiftGap_mono {y z a : ℝ} (hy : (12 : ℝ) ≤ y) (ha : 2 ≤ a) (hz : a ≤ z) :
    qNeOneHalfShiftGap y a ≤ qNeOneHalfShiftGap y z := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hp := mul_nonneg (sq_nonneg y) (show 0 ≤ z + a - 4 by linarith only [ha, hz])
  have hc :
    0 ≤
      2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (1341 / 1000 : ℝ) * y ^ 2 + (769 / 100 : ℝ) * y -
        3103 / 1000 := by
    nlinarith only [pow_nonneg hy0 3, sq_nonneg y, hp, hy]
  have he :
    qNeOneHalfShiftGap y z - qNeOneHalfShiftGap y a =
      (z - a) *
        (2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (1341 / 1000 : ℝ) * y ^ 2 + (769 / 100 : ℝ) * y -
          3103 / 1000) := by
    unfold qNeOneHalfShiftGap qNeOneDeciShiftGap qNeOneRetainedGap
    ring
  exact sub_nonneg.mp (he ▸ mul_nonneg (sub_nonneg.mpr hz) hc)

/-- For y>=12 the half-shift gap at the rational minorant is positive.
Clear the denominator and shift by twelve; all six coefficients are positive.
This certifies the entire half-line with one exact polynomial identity. -/
theorem qNeOneHalfShiftGap_rational_pos {y : ℝ} (hy : (12 : ℝ) ≤ y) :
    0 < qNeOneHalfShiftGap y (qNeOneHalfShiftLogLower y) := by
  have hv : 0 ≤ y - 12 := sub_nonneg.mpr hy
  have hsum : 0 < y + 12 := by linarith only [hy]
  have he :
    (y + 12) ^ 2 * qNeOneHalfShiftGap y (qNeOneHalfShiftLogLower y) =
      (12127 / 5000 : ℝ) * (y - 12) ^ 5 + (26891927 / 150000 : ℝ) * (y - 12) ^ 4 +
        (82665301 / 18750 : ℝ) * (y - 12) ^ 3 +
        (34435713181 / 750000 : ℝ) * (y - 12) ^ 2 +
        (2907000511 / 15625 : ℝ) * (y - 12) +
        1953290892 / 15625 := by
    unfold qNeOneHalfShiftGap qNeOneDeciShiftGap qNeOneRetainedGap qNeOneHalfShiftLogLower
    field_simp [hsum.ne']
    ring
  have hp : 0 < (y + 12) ^ 2 * qNeOneHalfShiftGap y (qNeOneHalfShiftLogLower y) := by
    nlinarith only [he, pow_nonneg hv 5, pow_nonneg hv 4, pow_nonneg hv 3, sq_nonneg (y - 12), hv]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hsum)).mp hp

/-- The logarithm of twelve exceeds 621/250. A short rational Taylor
interval proves the anchor. This is a constant check rather than an input table. -/
theorem qNeOneHalfShift_log_anchor : (621 / 250 : ℝ) < Real.log 12 := by
  have hc : Analysis.rationalLogIntervalCheck 12 4 12 (24849 / 10000) (24850 / 10000) = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h]

/-- Above twelve, the rational minorant lies below the real logarithm.
Use the anchored chord bound and normalize its denominator.
This connects the exact polynomial certificate to the actual logarithm. -/
theorem qNeOneHalfShift_log_lower {y : ℝ} (hy : (12 : ℝ) ≤ y) :
    qNeOneHalfShiftLogLower y ≤ Real.log y := by
  have h :=
    Analysis.log_gt_affine_of_anchor (by norm_num only : (0 : ℝ) < 12) hy hy (le_refl y)
      qNeOneHalfShift_log_anchor
  have he : 621 / 250 + 2 / (12 + y) * (y - 12) = qNeOneHalfShiftLogLower y := by
    unfold qNeOneHalfShiftLogLower
    rw [add_comm (12 : ℝ) y]
    ring
  rw [he] at h
  exact h.le

/-- Above twelve the actual logarithm gives a positive half-shift gap.
Combine minorant positivity and monotonicity. This is the analytic separation. -/
theorem qNeOneHalfShiftGap_pos {y : ℝ} (hy : (12 : ℝ) ≤ y) :
    0 < qNeOneHalfShiftGap y (Real.log y) := by
  have hn : 0 ≤ 2 * (y - 12) / (y + 12) :=
    div_nonneg (mul_nonneg (by norm_num only) (sub_nonneg.mpr hy)) (by linarith only [hy])
  have ha : (2 : ℝ) ≤ qNeOneHalfShiftLogLower y := by
    unfold qNeOneHalfShiftLogLower
    linarith only [hn]
  exact
    (qNeOneHalfShiftGap_rational_pos hy).trans_le
      (qNeOneHalfShiftGap_mono hy ha (qNeOneHalfShift_log_lower hy))

/-- Above eight, changing the conductor input by c changes the scaled
upper envelope by the exact displayed affine cost. The other inputs are arbitrary.
Normalize the scaled identity. This supports further conductor allowances. -/
theorem qNeOneReciprocalUpper_scaled_conductor_shift {y f r d c : ℝ} (hy : (8 : ℝ) ≤ y) :
    (y - 1) ^ 2 * (qNeOneReciprocalUpper y (f + c) r d - qNeOneReciprocalUpper y f r d) =
      c * ((2 * y + 2 + 2 * Real.log y) * (y ^ 2 - 1) / 2 + Real.log y * (y - 1) ^ 2) := by
  rw [mul_sub, qNeOneReciprocalUpper_scaled_eq hy, qNeOneReciprocalUpper_scaled_eq hy]
  ring

/-- For root y>=12 and conductor level L<=y+1/2, the fixed upper envelope
is strictly below the Riemann lower envelope. Transport the one-tenth cap by
its exact affine cost and use half-shift gap positivity.
This yields a larger root saving without finite input certificates. -/
theorem qNeOneHalfShiftUpper_lt_lower {y L : ℝ} (hy : (12 : ℝ) ≤ y) (hL : L ≤ y + 1 / 2) :
    qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (1483 / 1000) (Real.log 2) <
      qNeOneReciprocalLower y := by
  have h8 : (8 : ℝ) ≤ y := by linarith only [hy]
  have hu := qNeOneDeciShiftUpper_scaled_le h8 (show L - 2 / 5 ≤ y + 1 / 10 by linarith only [hL])
  have hs :=
    qNeOneReciprocalUpper_scaled_conductor_shift (f := L - 2 / 5 + Real.log 4 - Real.log Real.pi)
      (r := (1483 / 1000 : ℝ)) (d := Real.log 2) (c := (2 / 5 : ℝ)) h8
  have hf :
    L - 2 / 5 + Real.log 4 - Real.log Real.pi + 2 / 5 = L + Real.log 4 - Real.log Real.pi := by ring
  rw [hf] at hs
  have hid :
    (y - 1) ^ 2 * qNeOneReciprocalLower y - qNeOneDeciShiftUpperScaledCap y (Real.log y) -
        (2 / 5 : ℝ) * ((2 * y + 2 + 2 * Real.log y) * (y ^ 2 - 1) / 2 + Real.log y * (y - 1) ^ 2) =
      qNeOneHalfShiftGap y (Real.log y) := by
    unfold qNeOneReciprocalLower qNeOneDeciShiftUpperScaledCap qNeOneHalfShiftGap qNeOneDeciShiftGap
      qNeOneRetainedGap
    ring
  have hp := qNeOneHalfShiftGap_pos hy
  by_contra h
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg (y - 1))
  nlinarith only [hu, hs, hid, hp, hm]

end PseudoPrime.LLS.Extensions
