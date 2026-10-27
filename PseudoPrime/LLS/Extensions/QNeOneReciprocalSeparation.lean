/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneReciprocalTransfer

/-! # Whole-half-line separation for the reciprocal quadratic branches -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The cleared gap polynomial at root y and logarithm z, after allowing
conductor level at most y+1/1000 and reciprocal loss 789/500.
Its positivity certifies the odd-prime three-branch contradiction. -/
noncomputable def qNeOneReciprocalGap (y z : ℝ) : ℝ :=
  2 * y ^ 3 * z - (3896 / 625 : ℝ) * y ^ 3 + 4 * y ^ 2 * z ^ 2 - (533 / 1000 : ℝ) * y ^ 2 * z -
        (9589 / 3750 : ℝ) * y ^ 2 +
      (1673 / 250 : ℝ) * y * z +
      (15461 / 3750 : ℝ) * y -
    (3103 / 1000 : ℝ) * z -
    2288 / 1875

/-- For y at least 17/2 and logarithm arguments at least two, the cleared
gap increases with its second argument. Factor the difference and certify
its nonnegative coefficient. This permits a rational logarithm lower bound. -/
theorem qNeOneReciprocalGap_mono {y z a : ℝ} (hy : (17 / 2 : ℝ) ≤ y) (ha : 2 ≤ a) (hz : a ≤ z) :
    qNeOneReciprocalGap y a ≤ qNeOneReciprocalGap y z := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hp := mul_nonneg (sq_nonneg y) (show 0 ≤ z + a - 4 by linarith only [ha, hz])
  have hc :
    0 ≤
      2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (533 / 1000 : ℝ) * y ^ 2 + (1673 / 250 : ℝ) * y -
        3103 / 1000 := by
    nlinarith only [pow_nonneg hy0 3, sq_nonneg y, hp, hy]
  have he :
    qNeOneReciprocalGap y z - qNeOneReciprocalGap y a =
      (z - a) *
        (2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (533 / 1000 : ℝ) * y ^ 2 + (1673 / 250 : ℝ) * y -
          3103 / 1000) := by
    unfold qNeOneReciprocalGap
    ring
  exact sub_nonneg.mp (he ▸ mul_nonneg (sub_nonneg.mpr hz) hc)

/-- The logarithm of 17/2 is strictly above 107/50.
A short rational Taylor interval proves the anchor without a numerical oracle.
This is the only log anchor in the whole-half-line separation. -/
theorem reciprocal_log_anchor : (107 / 50 : ℝ) < Real.log (17 / 2) := by
  have hc :
    Analysis.rationalLogIntervalCheck (17 / 2) 3 8 (214001 / 100000) (214007 / 100000) = true := by
    decide +kernel
  have h := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  linarith only [h]

/-- The rational logarithm minorant 107/50+2(y-17/2)/(y+17/2).
It is valid for y at least 17/2. Retaining its denominator avoids
partitioning the unbounded analytic range into finite intervals. -/
noncomputable def qNeOneReciprocalLogLower (y : ℝ) : ℝ :=
  107 / 50 + 2 * (y - 17 / 2) / (y + 17 / 2)

/-- For y at least 17/2, the rational minorant is at most log y.
Apply the anchored logarithm chord with the upper endpoint equal to y.
This supplies one rational lower bound over the entire half-line. -/
theorem reciprocal_log_rational {y : ℝ} (hy : (17 / 2 : ℝ) ≤ y) :
    qNeOneReciprocalLogLower y ≤ Real.log y := by
  have h :=
    Analysis.log_gt_affine_of_anchor (by norm_num only : (0 : ℝ) < 17 / 2) hy hy (le_refl y)
      reciprocal_log_anchor
  have he : 107 / 50 + 2 / (17 / 2 + y) * (y - 17 / 2) = qNeOneReciprocalLogLower y := by
    unfold qNeOneReciprocalLogLower
    rw [add_comm (17 / 2 : ℝ) y]
    ring
  rw [he] at h
  exact h.le

/-- Above 17/2, the cleared gap evaluated at its rational log minorant
is strictly positive. Clear the positive denominator and shift by 17/2;
all six coefficients of the resulting polynomial are positive. -/
theorem qNeOneReciprocalGap_rational_pos {y : ℝ} (hy : (17 / 2 : ℝ) ≤ y) :
    0 < qNeOneReciprocalGap y (qNeOneReciprocalLogLower y) := by
  have hv : 0 ≤ y - 17 / 2 := sub_nonneg.mpr hy
  have hsum : 0 < y + 17 / 2 := by linarith only [hy]
  have he :
    (y + 17 / 2) ^ 2 * qNeOneReciprocalGap y (qNeOneReciprocalLogLower y) =
      (1279 / 625 : ℝ) * (y - 17 / 2) ^ 5 + (17633327 / 150000 : ℝ) * (y - 17 / 2) ^ 4 +
        (314489369 / 150000 : ℝ) * (y - 17 / 2) ^ 3 +
        (9111200927 / 600000 : ℝ) * (y - 17 / 2) ^ 2 +
        (3930893357 / 100000 : ℝ) * (y - 17 / 2) +
        318111837 / 200000 := by
    unfold qNeOneReciprocalGap qNeOneReciprocalLogLower
    field_simp [hsum.ne']
    ring
  have hp : 0 < (y + 17 / 2) ^ 2 * qNeOneReciprocalGap y (qNeOneReciprocalLogLower y) := by
    nlinarith only [he, pow_nonneg hv 5, pow_nonneg hv 4, pow_nonneg hv 3, sq_nonneg (y - 17 / 2),
      hv]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hsum)).mp hp

/-- The cleared gap at the actual logarithm is positive for every y at
least 17/2. Combine the rational minorant, monotonicity and polynomial
positivity. No finite grid or compact-cover certificate is used. -/
theorem qNeOneReciprocalGap_pos {y : ℝ} (hy : (17 / 2 : ℝ) ≤ y) :
    0 < qNeOneReciprocalGap y (Real.log y) := by
  have hn : 0 ≤ 2 * (y - 17 / 2) / (y + 17 / 2) :=
    div_nonneg (mul_nonneg (by norm_num only) (sub_nonneg.mpr hy)) (by linarith only [hy])
  have ha : (2 : ℝ) ≤ qNeOneReciprocalLogLower y := by
    unfold qNeOneReciprocalLogLower
    linarith only [hn]
  exact
    (qNeOneReciprocalGap_rational_pos hy).trans_le
      (qNeOneReciprocalGap_mono hy ha (reciprocal_log_rational hy))

/-- For y at least eight, multiplying the upper envelope by (y-1)^2
clears its reciprocal denominator. Normalize the exact rational identity.
This keeps the scaling reusable for arbitrary conductor and loss bounds. -/
theorem qNeOneReciprocalUpper_scaled_eq {y f r d : ℝ} (hy : 8 ≤ y) :
    (y - 1) ^ 2 * qNeOneReciprocalUpper y f r d =
      (2 * y + 2 + 2 * Real.log y) *
          ((1 / 2) * (y ^ 2 - 1) * f + (r - 4 / 5 + d - 2 * Real.log y) * y ^ 2) +
        (f * Real.log y + Analysis.primitiveLogEvenMainError (y ^ 2)) * (y - 1) ^ 2 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hsub : y - 1 ≠ 0 := by linarith only [hy]
  have he : 1 - 1 / y = (y - 1) / y := by field_simp [hy0.ne']
  unfold qNeOneReciprocalUpper
  rw [he]
  field_simp [hy0.ne', hsub]
  ring

/-- The rational upper expression after denominator clearing.
The conductor excess is 243/1000 and the reciprocal numerator cost is 184/125;
the even error retains its negative squared logarithm. This defines the gap. -/
noncomputable def qNeOneReciprocalUpperScaledCap (y z : ℝ) : ℝ :=
  (2 * y + 2 + 2 * z) * ((1 / 2) * (y ^ 2 - 1) * (y + 243 / 1000) + (184 / 125 - 2 * z) * y ^ 2) +
    ((y + 243 / 1000) * z + 5 / 12 - (23 / 40) * z - 2 * z ^ 2) * (y - 1) ^ 2

/-- The conductor correction log 4-log pi is at most 121/500.
Use the precise rational lower bound for log pi and the log-two certificate.
This improves the former quarter allowance. -/
theorem log_four_sub_log_pi_le_121_div_500 : Real.log 4 - Real.log Real.pi ≤ (121 / 500 : ℝ) := by
  rw [Real.log_four_eq]
  linarith only [Analysis.log_pi_ge_2096_div_1831, Real.log_two_lt_d9]

/-- For y at least eight and conductor level L at most y+1/1000,
the scaled upper envelope is bounded by the rational cap.
Retain the even error, the precise conductor correction and reciprocal loss.
This connects the arithmetic upper estimate to the gap polynomial. -/
theorem qNeOneReciprocalUpper_scaled_le {y L : ℝ} (hy : 8 ≤ y) (hL : L ≤ y + 1 / 1000) :
    (y - 1) ^ 2 *
        qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (789 / 500) (Real.log 2) ≤
      qNeOneReciprocalUpperScaledCap y (Real.log y) := by
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hF : L + Real.log 4 - Real.log Real.pi ≤ y + 243 / 1000 := by
    linarith only [hL, log_four_sub_log_pi_le_121_div_500]
  have hFm :=
    mul_le_mul_of_nonneg_left hF (show 0 ≤ (1 / 2 : ℝ) * (y ^ 2 - 1) by nlinarith only [hy])
  have htwo : (789 / 500 : ℝ) - 4 / 5 + Real.log 2 ≤ 184 / 125 := by
    linarith only [Real.log_two_lt_d9]
  have htm := mul_le_mul_of_nonneg_right htwo (sq_nonneg y)
  have hb :
    (1 / 2 : ℝ) * (y ^ 2 - 1) * (L + Real.log 4 - Real.log Real.pi) +
        (789 / 500 - 4 / 5 + Real.log 2 - 2 * Real.log y) * y ^ 2 ≤
      (1 / 2 : ℝ) * (y ^ 2 - 1) * (y + 243 / 1000) + (184 / 125 - 2 * Real.log y) * y ^ 2 := by
    nlinarith only [hFm, htm]
  have hc :=
    mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * y + 2 + 2 * Real.log y by linarith only [hy, hz])
  have hg :=
    mul_le_mul_of_nonneg_right Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant.le hz
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
  have he :
    Analysis.primitiveLogEvenMainError (y ^ 2) ≤
      5 / 12 - (23 / 40 : ℝ) * Real.log y - 2 * (Real.log y) ^ 2 := by
    unfold Analysis.primitiveLogEvenMainError
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hg, hpi]
  have hfz := mul_le_mul_of_nonneg_right hF hz
  have hes :
    (L + Real.log 4 - Real.log Real.pi) * Real.log y + Analysis.primitiveLogEvenMainError (y ^ 2) ≤
      (y + 243 / 1000) * Real.log y + 5 / 12 - (23 / 40 : ℝ) * Real.log y -
        2 * (Real.log y) ^ 2 := by
    linarith only [hfz, he]
  have hem := mul_le_mul_of_nonneg_right hes (sq_nonneg (y - 1))
  have hid :=
    qNeOneReciprocalUpper_scaled_eq (f := L + Real.log 4 - Real.log Real.pi) (r := (789 / 500 : ℝ))
      (d := Real.log 2) hy
  unfold qNeOneReciprocalUpperScaledCap
  linarith only [hid, hc, hem]

/-- For y at least 17/2 and level L at most y+1/1000, the upper envelope
is strictly below the precise Riemann lower envelope. Use the cleared
identity and whole-half-line polynomial positivity. The root may be smaller
than the logarithmic level, giving a strict witness bound. -/
theorem qNeOneReciprocalUpper_lt_lower {y L : ℝ} (hy : (17 / 2 : ℝ) ≤ y) (hL : L ≤ y + 1 / 1000) :
    qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (789 / 500) (Real.log 2) <
      qNeOneReciprocalLower y := by
  have h8 : (8 : ℝ) ≤ y := by linarith only [hy]
  have hu := qNeOneReciprocalUpper_scaled_le h8 hL
  have hid :
    (y - 1) ^ 2 * qNeOneReciprocalLower y - qNeOneReciprocalUpperScaledCap y (Real.log y) =
      qNeOneReciprocalGap y (Real.log y) := by
    unfold qNeOneReciprocalLower qNeOneReciprocalUpperScaledCap qNeOneReciprocalGap
    ring
  have hp := qNeOneReciprocalGap_pos hy
  by_contra h
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg (y - 1))
  linarith only [hu, hid, hp, hm]

/-- Under GRH, the three values at two and the stated conductor bounds,
odd-prime triviality is impossible when y is at least 17/2 and L at most
y+1/1000. Insert the certified reciprocal loss and global separation into
the generic three-branch transfer theorem. -/
theorem not_oddPrimeTrivial_of_reciprocal_entrance {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hne : χ ≠ 1) (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y L : ℝ} (hy : (17 / 2 : ℝ) ≤ y)
    (hL : L ≤ y + 1 / 1000) (hlog4 : Real.log χ.conductor ≤ L + Real.log 4)
    (hlogOdd : χ.primitiveCharacter 2 ≠ 0 → Real.log χ.conductor ≤ L)
    (hcases :
      χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1) :
    ¬OddPrimeTrivial χ (y ^ 2) := by
  have h8 : (8 : ℝ) ≤ y := by linarith only [hy]
  have hx := Analysis.sq_ge_64_of_ge_8 h8
  exact
    not_oddPrimeTrivial_of_reciprocal_loss χ hne heven hGRH h8 hlog4 hlogOdd hcases
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_789_div_500
        hGRH.riemann (le_trans (by norm_num only) hx))
      (qNeOneReciprocalUpper_lt_lower hy hL)

end PseudoPrime.LLS.Extensions
