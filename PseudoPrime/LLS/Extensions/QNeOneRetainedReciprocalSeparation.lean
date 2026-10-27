/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneReciprocalSeparation

/-! # Whole-half-line separation for the reciprocal quadratic branches -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The cleared gap polynomial at root y and logarithm z, after allowing
conductor level at most y+1/1000 and effective reciprocal loss 1483/1000.
Its positivity certifies the odd-prime three-branch contradiction. -/
noncomputable def qNeOneRetainedGap (y z : ℝ) : ℝ :=
  2 * y ^ 3 * z - (15109 / 2500 : ℝ) * y ^ 3 + 4 * y ^ 2 * z ^ 2 - (343 / 1000 : ℝ) * y ^ 2 * z -
        (17753 / 7500 : ℝ) * y ^ 2 +
      (1673 / 250 : ℝ) * y * z +
      (15461 / 3750 : ℝ) * y -
    (3103 / 1000 : ℝ) * z -
    2288 / 1875

/-- For y at least 8 and logarithm arguments at least two, the cleared
gap increases with its second argument. Factor the difference and certify
its nonnegative coefficient. This permits a rational logarithm lower bound. -/
theorem qNeOneRetainedGap_mono {y z a : ℝ} (hy : (8 : ℝ) ≤ y) (ha : 2 ≤ a) (hz : a ≤ z) :
    qNeOneRetainedGap y a ≤ qNeOneRetainedGap y z := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hp := mul_nonneg (sq_nonneg y) (show 0 ≤ z + a - 4 by linarith only [ha, hz])
  have hc :
    0 ≤
      2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (343 / 1000 : ℝ) * y ^ 2 + (1673 / 250 : ℝ) * y -
        3103 / 1000 := by
    nlinarith only [pow_nonneg hy0 3, sq_nonneg y, hp, hy]
  have he :
    qNeOneRetainedGap y z - qNeOneRetainedGap y a =
      (z - a) *
        (2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (343 / 1000 : ℝ) * y ^ 2 + (1673 / 250 : ℝ) * y -
          3103 / 1000) := by
    unfold qNeOneRetainedGap
    ring
  exact sub_nonneg.mp (he ▸ mul_nonneg (sub_nonneg.mpr hz) hc)

/-- The logarithm of 8 is strictly above 2079/1000.
The certified logarithm of two gives this anchor without a numerical oracle.
This is the only log anchor in the whole-half-line separation. -/
theorem retained_reciprocal_log_anchor : (2079 / 1000 : ℝ) < Real.log 8 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [Real.log_two_gt_d9]

/-- The rational logarithm minorant 2079/1000+2(y-8)/(y+8).
It is valid for y at least 8. Retaining its denominator avoids
partitioning the unbounded analytic range into finite intervals. -/
noncomputable def qNeOneRetainedLogLower (y : ℝ) : ℝ :=
  2079 / 1000 + 2 * (y - 8) / (y + 8)

/-- For y at least 8, the rational minorant is at most log y.
Apply the anchored logarithm chord with the upper endpoint equal to y.
This supplies one rational lower bound over the entire half-line. -/
theorem retained_reciprocal_log_rational {y : ℝ} (hy : (8 : ℝ) ≤ y) :
    qNeOneRetainedLogLower y ≤ Real.log y := by
  have h :=
    Analysis.log_gt_affine_of_anchor (by norm_num only : (0 : ℝ) < 8) hy hy (le_refl y)
      retained_reciprocal_log_anchor
  have he : 2079 / 1000 + 2 / (8 + y) * (y - 8) = qNeOneRetainedLogLower y := by
    unfold qNeOneRetainedLogLower
    rw [add_comm (8 : ℝ) y]
    ring
  rw [he] at h
  exact h.le

/-- Above 8, the cleared gap evaluated at its rational log minorant
is strictly positive. Clear the positive denominator and shift by 8;
all six coefficients of the resulting polynomial are positive. -/
theorem qNeOneRetainedGap_rational_pos {y : ℝ} (hy : (8 : ℝ) ≤ y) :
    0 < qNeOneRetainedGap y (qNeOneRetainedLogLower y) := by
  have hv : 0 ≤ y - 8 := sub_nonneg.mpr hy
  have hsum : 0 < y + 8 := by linarith only [hy]
  have he :
    (y + 8) ^ 2 * qNeOneRetainedGap y (qNeOneRetainedLogLower y) =
      (2643 / 1250 : ℝ) * (y - 8) ^ 5 + (351579601 / 3000000 : ℝ) * (y - 8) ^ 4 +
        (1517286313 / 750000 : ℝ) * (y - 8) ^ 3 +
        (14499764527 / 1000000 : ℝ) * (y - 8) ^ 2 +
        (758524849 / 18750 : ℝ) * (y - 8) +
        193318628 / 9375 := by
    unfold qNeOneRetainedGap qNeOneRetainedLogLower
    field_simp [hsum.ne']
    ring
  have hp : 0 < (y + 8) ^ 2 * qNeOneRetainedGap y (qNeOneRetainedLogLower y) := by
    nlinarith only [he, pow_nonneg hv 5, pow_nonneg hv 4, pow_nonneg hv 3, sq_nonneg (y - 8), hv]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hsum)).mp hp

/-- The cleared gap at the actual logarithm is positive for every y at
least 8. Combine the rational minorant, monotonicity and polynomial
positivity. No finite grid or compact-cover certificate is used. -/
theorem qNeOneRetainedGap_pos {y : ℝ} (hy : (8 : ℝ) ≤ y) :
    0 < qNeOneRetainedGap y (Real.log y) := by
  have hn : 0 ≤ 2 * (y - 8) / (y + 8) :=
    div_nonneg (mul_nonneg (by norm_num only) (sub_nonneg.mpr hy)) (by linarith only [hy])
  have ha : (2 : ℝ) ≤ qNeOneRetainedLogLower y := by
    unfold qNeOneRetainedLogLower
    linarith only [hn]
  exact
    (qNeOneRetainedGap_rational_pos hy).trans_le
      (qNeOneRetainedGap_mono hy ha (retained_reciprocal_log_rational hy))

/-- The rational upper expression after denominator clearing.
The conductor excess is 243/1000 and the reciprocal numerator cost is 1377/1000;
the even error retains its negative squared logarithm. This defines the gap. -/
noncomputable def qNeOneRetainedUpperScaledCap (y z : ℝ) : ℝ :=
  (2 * y + 2 + 2 * z) * ((1 / 2) * (y ^ 2 - 1) * (y + 243 / 1000) + (1377 / 1000 - 2 * z) * y ^ 2) +
    ((y + 243 / 1000) * z + 5 / 12 - (23 / 40) * z - 2 * z ^ 2) * (y - 1) ^ 2

/-- For y at least eight and conductor level L at most y+1/1000,
the scaled upper envelope is bounded by the rational cap.
Retain the even error, the precise conductor correction and reciprocal loss.
This connects the arithmetic upper estimate to the gap polynomial. -/
theorem qNeOneRetainedUpper_scaled_le {y L : ℝ} (hy : 8 ≤ y) (hL : L ≤ y + 1 / 1000) :
    (y - 1) ^ 2 *
        qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (1483 / 1000) (Real.log 2) ≤
      qNeOneRetainedUpperScaledCap y (Real.log y) := by
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hF : L + Real.log 4 - Real.log Real.pi ≤ y + 243 / 1000 := by
    linarith only [hL, log_four_sub_log_pi_le_121_div_500]
  have hFm :=
    mul_le_mul_of_nonneg_left hF (show 0 ≤ (1 / 2 : ℝ) * (y ^ 2 - 1) by nlinarith only [hy])
  have htwo : (1483 / 1000 : ℝ) - 4 / 5 + Real.log 2 ≤ 1377 / 1000 := by
    linarith only [Real.log_two_lt_d9]
  have htm := mul_le_mul_of_nonneg_right htwo (sq_nonneg y)
  have hb :
    (1 / 2 : ℝ) * (y ^ 2 - 1) * (L + Real.log 4 - Real.log Real.pi) +
        (1483 / 1000 - 4 / 5 + Real.log 2 - 2 * Real.log y) * y ^ 2 ≤
      (1 / 2 : ℝ) * (y ^ 2 - 1) * (y + 243 / 1000) + (1377 / 1000 - 2 * Real.log y) * y ^ 2 := by
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
    qNeOneReciprocalUpper_scaled_eq (f := L + Real.log 4 - Real.log Real.pi) (r :=
      (1483 / 1000 : ℝ)) (d := Real.log 2) hy
  unfold qNeOneRetainedUpperScaledCap
  linarith only [hid, hc, hem]

/-- For y at least 8 and level L at most y+1/1000, the upper envelope
is strictly below the precise Riemann lower envelope. Use the cleared
identity and whole-half-line polynomial positivity. The root may be smaller
than the logarithmic level, giving a strict witness bound. -/
theorem qNeOneRetainedUpper_lt_lower {y L : ℝ} (hy : (8 : ℝ) ≤ y) (hL : L ≤ y + 1 / 1000) :
    qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (1483 / 1000) (Real.log 2) <
      qNeOneReciprocalLower y := by
  have h8 : (8 : ℝ) ≤ y := by linarith only [hy]
  have hu := qNeOneRetainedUpper_scaled_le h8 hL
  have hid :
    (y - 1) ^ 2 * qNeOneReciprocalLower y - qNeOneRetainedUpperScaledCap y (Real.log y) =
      qNeOneRetainedGap y (Real.log y) := by
    unfold qNeOneReciprocalLower qNeOneRetainedUpperScaledCap qNeOneRetainedGap
    ring
  have hp := qNeOneRetainedGap_pos hy
  by_contra h
  have hm := mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg (y - 1))
  linarith only [hu, hid, hp, hm]

/-- Under GRH, the three values at two and the stated conductor bounds,
odd-prime triviality is impossible when y is at least 8 and L at most
y+1/1000. Insert the certified reciprocal loss and global separation into
the generic three-branch transfer theorem. -/
theorem not_oddPrimeTrivial_of_retained_reciprocal_entrance {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y L : ℝ} (hy : (8 : ℝ) ≤ y)
    (hL : L ≤ y + 1 / 1000) (hlog4 : Real.log χ.conductor ≤ L + Real.log 4)
    (hlogOdd : χ.primitiveCharacter 2 ≠ 0 → Real.log χ.conductor ≤ L)
    (hcases :
      χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1) :
    ¬OddPrimeTrivial χ (y ^ 2) := by
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hE := Analysis.primitiveReciprocalEvenMainError_le_neg_179_div_200 hx
  have he : (789 / 500 : ℝ) + -(179 / 200) + 4 / 5 = 1483 / 1000 := by norm_num only
  apply
    not_oddPrimeTrivial_of_reciprocal_loss_and_mainError χ hne heven hGRH hy hE hlog4 hlogOdd hcases
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_789_div_500
        hGRH.riemann (le_trans (by norm_num only) hx))
  simpa only [he] using qNeOneRetainedUpper_lt_lower hy hL

end PseudoPrime.LLS.Extensions
