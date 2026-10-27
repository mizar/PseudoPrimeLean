/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneLogWeightedBounds

/-! # Sharper Riemann lower bounds for the small-scale quadratic non-one comparison -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- The Riemann lower envelope retaining the certified zero mass and logarithmic constant.
The input is a positive real cutoff root y and the output is a lower comparison value.
This keeps the half-square dyadic defect but avoids coarse bounds on the two Riemann terms. -/
noncomputable def qNeOneSharpLowerBound (y : ℝ) : ℝ :=
  y ^ 2 - (y + 1) / 8 - (1839 / 500 : ℝ) * Real.log y - 1 - 2 * (Real.log y) ^ 2

/-- Input: a cutoff root at least eight.
Claim: the sharper envelope is below the actual Riemann lower bound minus the dyadic defect.
Proof: use the certified zero mass 1/16 and logarithmic constant 1839/1000.
This replaces the common lower envelope without changing any character-sum identity. -/
theorem qNeOneSharpLowerBound_le_riemann_lower {y : ℝ} (hy : 8 ≤ y) :
    qNeOneSharpLowerBound y ≤ riemannLogLowerAt (y ^ 2) - (Real.log (y ^ 2)) ^ 2 / 2 := by
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_sixteenth
      (show 0 ≤ y + 1 by linarith only [hy])
  have hl :=
    mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le
      (Real.log_nonneg (show 1 ≤ y by linarith only [hy]))
  rw [qNeOneSharpLowerBound, riemannLogLowerAt, Real.sqrt_sq (show 0 ≤ y by linarith only [hy]),
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hm, hl]

/-- Input: a cutoff root at least eight.
Claim: the previous common lower envelope is no greater than the sharper one.
Proof: the retained Riemann coefficients are smaller and both factors are nonnegative.
This permits reuse of the already proved unbounded comparison. -/
theorem qNeOneAnalyticLowerBound_le_sharp {y : ℝ} (hy : 8 ≤ y) :
    qNeOneAnalyticLowerBound y ≤ qNeOneSharpLowerBound y := by
  have hz : 0 ≤ Real.log y := Real.log_nonneg (show 1 ≤ y by linarith only [hy])
  unfold qNeOneAnalyticLowerBound qNeOneSharpLowerBound
  nlinarith only [hy, hz]

/-- Claim: log(99/10) is strictly greater than 229/100.
Proof: factor 99/10 as nine times 11/10 and use the positive logarithm chord.
This is the only logarithmic anchor needed for the new compact real interval. -/
theorem log_ninety_nine_tenths_gt : (229 / 100 : ℝ) < Real.log (99 / 10) := by
  have hc := Real.lt_log_one_add_of_pos (by norm_num only : (0 : ℝ) < 1 / 10)
  rw [show (99 / 10 : ℝ) = 3 ^ 2 * (1 + 1 / 10) by norm_num only,
    Real.log_mul (by norm_num only : (3 ^ 2 : ℝ) ≠ 0) (by norm_num only : (1 + 1 / 10 : ℝ) ≠ 0),
    Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hc, Real.log_three_gt_d9]

/-- Input: 99/10 ≤ y ≤ 12.
Claim: log y lies above the displayed affine lower bound.
Proof: apply the existing anchor inequality and weaken its positive slope.
This allows a polynomial separation on the whole compact real interval. -/
theorem log_ge_small_scale_affine {y : ℝ} (hy : (99 / 10 : ℝ) ≤ y) (hu : y ≤ 12) :
    229 / 100 + (y - 99 / 10) / 12 ≤ Real.log y := by
  have hc :=
    Analysis.log_gt_affine_of_anchor (by norm_num only : (0 : ℝ) < 99 / 10)
      (by norm_num only : (99 / 10 : ℝ) ≤ 12) hy hu log_ninety_nine_tenths_gt
  norm_num only at hc
  linarith only [hc, hy]

/-- Claim: the even conductor correction log(4)-log(pi) is at most one quarter.
Proof: combine explicit logarithms of two and three with a lower estimate for log(pi/3).
This keeps the conductor correction small at the new analytic start. -/
theorem log_four_sub_log_pi_le_quarter : Real.log 4 - Real.log Real.pi ≤ (1 / 4 : ℝ) := by
  have hlog4 : Real.log (4 : ℝ) ≤ 139 / 100 := by
    rw [Real.log_four_eq]
    linarith only [Real.log_two_lt_d9]
  have hpi : (314 / 100 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d2
    norm_num only at h ⊢
    exact h
  have hx : (7 / 150 : ℝ) < Real.pi / 3 - 1 := by linarith only [hpi]
  have hxpos : 0 < Real.pi / 3 - 1 := lt_trans (by norm_num only) hx
  have hlogadd := Real.lt_log_one_add_of_pos hxpos
  have hlogone : Real.log (1 + (Real.pi / 3 - 1)) = Real.log (Real.pi / 3) := by
    congr 1
    ring
  rw [hlogone, Real.log_div Real.pi_ne_zero (by norm_num only : (3 : ℝ) ≠ 0)] at hlogadd
  have hfrac : (9 / 200 : ℝ) < 2 * (Real.pi / 3 - 1) / (Real.pi / 3 - 1 + 2) := by
    apply (lt_div_iff₀ (add_pos_of_pos_of_nonneg hxpos (by norm_num only))).2
    linarith only [hx]
  linarith only [hlog4, hlogadd, hfrac, Real.log_three_gt_d9]

/-- The cleared rational lower estimate for the sharp zero-branch gap.
Inputs are a cutoff root y and its logarithm z; coefficients are explicit rationals.
Positivity of this polynomial certifies the compact-interval comparison. -/
noncomputable def qNeOneSharpGapPolynomial (y z : ℝ) : ℝ :=
  2 * y ^ 3 * z - (51 / 8 : ℝ) * y ^ 3 + 4 * y ^ 2 * z ^ 2 - (339 / 500 : ℝ) * y ^ 2 * z -
        (61 / 24 : ℝ) * y ^ 2 +
      (857 / 125 : ℝ) * y * z +
      (101 / 24 : ℝ) * y -
    (1589 / 500 : ℝ) * z -
    31 / 24

/-- Input: a cutoff root at least 99/10 and z at least a at least two.
Claim: the cleared gap increases with its logarithm argument.
Proof: factor the difference and certify the nonnegative coefficient.
This transfers an affine logarithm lower bound to the exact gap. -/
theorem qNeOneSharpGapPolynomial_mono {y z a : ℝ} (hy : (99 / 10 : ℝ) ≤ y) (ha : 2 ≤ a)
    (hz : a ≤ z) : qNeOneSharpGapPolynomial y a ≤ qNeOneSharpGapPolynomial y z := by
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hza : 0 ≤ z + a - 4 := by linarith only [ha, hz]
  have hp := mul_nonneg (sq_nonneg y) hza
  have hc :
    0 ≤
      2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (339 / 500 : ℝ) * y ^ 2 + (857 / 125 : ℝ) * y -
        1589 / 500 := by
    nlinarith only [pow_nonneg hy0 3, sq_nonneg y, hp, hy]
  have he :
    qNeOneSharpGapPolynomial y z - qNeOneSharpGapPolynomial y a =
      (z - a) *
        (2 * y ^ 3 + 4 * y ^ 2 * (z + a) - (339 / 500 : ℝ) * y ^ 2 + (857 / 125 : ℝ) * y -
          1589 / 500) := by
    unfold qNeOneSharpGapPolynomial
    ring
  exact sub_nonneg.mp (he ▸ mul_nonneg (sub_nonneg.mpr hz) hc)

/-- Input: a cutoff root at least 99/10.
Claim: the cleared gap at the affine logarithm is positive.
Proof: translate by 99/10; all five polynomial coefficients are positive.
This is a single real-variable identity rather than an enumerated interval certificate. -/
theorem qNeOneSharpGapPolynomial_affine_pos {y : ℝ} (hy : (99 / 10 : ℝ) ≤ y) :
    0 < qNeOneSharpGapPolynomial y (229 / 100 + (y - 99 / 10) / 12) := by
  have hv : 0 ≤ y - 99 / 10 := sub_nonneg.mpr hy
  have he :
    qNeOneSharpGapPolynomial y (229 / 100 + (y - 99 / 10) / 12) =
      (7 / 36 : ℝ) * (y - 99 / 10) ^ 4 + (31051 / 6000 : ℝ) * (y - 99 / 10) ^ 3 +
        (1686703 / 37500 : ℝ) * (y - 99 / 10) ^ 2 +
        (137589469 / 1000000 : ℝ) * (y - 99 / 10) +
        760911091 / 7500000 := by
    unfold qNeOneSharpGapPolynomial
    ring
  nlinarith only [he, pow_nonneg hv 4, pow_nonneg hv 3, sq_nonneg (y - 99 / 10), hv]

/-- Input: a cutoff root between 99/10 and twelve.
Claim: the cleared gap at its actual logarithm is positive.
Proof: combine the affine logarithm lower bound, monotonicity and the positive polynomial.
This closes the compact real interval required by the sharper zero-branch estimate. -/
theorem qNeOneSharpGapPolynomial_pos {y : ℝ} (hy : (99 / 10 : ℝ) ≤ y) (hu : y ≤ 12) :
    0 < qNeOneSharpGapPolynomial y (Real.log y) := by
  exact
    (qNeOneSharpGapPolynomial_affine_pos hy).trans_le
      (qNeOneSharpGapPolynomial_mono hy (by linarith only [hy]) (log_ge_small_scale_affine hy hu))

/-- Input: a cutoff root at least eight.
Claim: the squared denominator clears the zero-branch Hadamard bound as displayed.
Proof: preserve the exact denominator and bound the two logarithmic constants.
This supplies the reciprocal input to the compact analytic separation. -/
theorem qNeOneBUpperBoundZeroStar_cleared {y : ℝ} (hy : 8 ≤ y) :
    (y - 1) ^ 2 * qNeOneBUpperBoundZeroStar y ≤
      (1 / 2 : ℝ) * (y ^ 2 - 1) * (y + 1 / 4) + (3 / 2 - 2 * Real.log y) * y ^ 2 := by
  have hy0 : 0 < y := by linarith only [hy]
  have hc := div_mul_cancel₀ (1 : ℝ) hy0.ne'
  have hd : (1 - 1 / y) * y = y - 1 := by nlinarith only [hc]
  have hn : 1 - 1 / y ≠ 0 := by
    intro h
    rw [h, zero_mul] at hd
    linarith only [hy, hd]
  have hd2 : (1 - 1 / y) ^ 2 * y ^ 2 = (y - 1) ^ 2 := by
    calc
      _ = ((1 - 1 / y) * y) ^ 2 := by ring
      _ = _ := by rw [hd]
  have hdiv :=
    div_mul_cancel₀
      ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - Real.log 2))
      (pow_ne_zero 2 hn)
  change qNeOneBUpperBoundZeroStar y * (1 - 1 / y) ^ 2 = _ at hdiv
  have hmul := congrArg (fun v : ℝ ↦ v * y ^ 2) hdiv
  have hleft :
    qNeOneBUpperBoundZeroStar y * (1 - 1 / y) ^ 2 * y ^ 2 =
      qNeOneBUpperBoundZeroStar y * (y - 1) ^ 2 := by
    rw [mul_assoc, hd2]
  rw [hleft] at hmul
  have hcancel := div_mul_cancel₀ (1 : ℝ) (sq_pos_of_pos hy0).ne'
  have hFcancel := congrArg (fun v : ℝ ↦ v * (y + Real.log 4 - Real.log Real.pi)) hcancel
  have hF :=
    mul_le_mul_of_nonneg_left log_four_sub_log_pi_le_quarter
      (show 0 ≤ y ^ 2 - 1 by nlinarith only [hy])
  have htwo : Real.log (2 : ℝ) ≤ 7 / 10 := by linarith only [Real.log_two_lt_d9]
  have htwomul := mul_le_mul_of_nonneg_right htwo (sq_nonneg y)
  nlinarith only [hmul, hFcancel, hF, htwomul]

/-- Input: a cutoff root in the compact interval from 99/10 to twelve.
Claim: the zero-branch upper bound is strictly below the sharper Riemann lower bound.
Proof: use the cleared Hadamard bound and a positive rational polynomial.
This certifies every real point of the interval without a numerical grid. -/
theorem qNeOneUpperBoundZeroStar_lt_sharp_compact {y : ℝ} (hy : (99 / 10 : ℝ) ≤ y) (hu : y ≤ 12) :
    qNeOneUpperBoundZeroStar y < qNeOneSharpLowerBound y := by
  have h8 : 8 ≤ y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (show 1 ≤ y by linarith only [hy])
  have hb := qNeOneBUpperBoundZeroStar_cleared h8
  have hc :=
    mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * y + 2 + 2 * Real.log y by linarith only [hy, hz])
  have hF := mul_le_mul_of_nonneg_right log_four_sub_log_pi_le_quarter hz
  have hgamma := mul_le_mul_of_nonneg_right Real.one_half_lt_eulerMascheroniConstant.le hz
  have hpi : Real.pi ^ 2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
  have hmain :
    Analysis.primitiveLogEvenMainError (y ^ 2) ≤
      5 / 12 - (1 / 2 : ℝ) * Real.log y - 2 * (Real.log y) ^ 2 := by
    unfold Analysis.primitiveLogEvenMainError
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [hgamma, hpi]
  have he :
    (y + Real.log 4 - Real.log Real.pi) * Real.log y + Analysis.primitiveLogEvenMainError (y ^ 2) ≤
      (y + 1 / 4) * Real.log y + 5 / 12 - (1 / 2 : ℝ) * Real.log y - 2 * (Real.log y) ^ 2 := by
    linarith only [hF, hmain]
  have he' := mul_le_mul_of_nonneg_right he (sq_nonneg (y - 1))
  have hid :
    (y - 1) ^ 2 * qNeOneSharpLowerBound y -
        ((2 * y + 2 + 2 * Real.log y) *
            ((1 / 2 : ℝ) * (y ^ 2 - 1) * (y + 1 / 4) + (3 / 2 - 2 * Real.log y) * y ^ 2) +
          ((y + 1 / 4) * Real.log y + 5 / 12 - (1 / 2 : ℝ) * Real.log y - 2 * (Real.log y) ^ 2) *
            (y - 1) ^ 2) =
      qNeOneSharpGapPolynomial y (Real.log y) := by
    unfold qNeOneSharpLowerBound qNeOneSharpGapPolynomial
    ring
  have hp := qNeOneSharpGapPolynomial_pos hy hu
  by_contra h
  have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg (y - 1))
  unfold qNeOneUpperBoundZeroStar at hmul
  nlinarith only [hc, he', hid, hp, hmul]

/-- Input: a cutoff root at least 99/10.
Claim: the common upper envelope of all character-at-two branches is below the sharper lower one.
Proof: use the new compact interval and the previously certified unbounded comparison.
This supplies a single strict separation for the entire new analytic range. -/
theorem qNeOneCommonUpperBound_lt_sharp {y : ℝ} (hy : (99 / 10 : ℝ) ≤ y) :
    qNeOneCommonUpperBound y < qNeOneSharpLowerBound y := by
  have h8 : 8 ≤ y := by linarith only [hy]
  by_cases hu : y ≤ 12
  · exact
      max_lt (qNeOneUpperBoundZeroStar_lt_sharp_compact hy hu)
        ((qNeOneAnalyticUpperBoundOne_lt_qNeOneAnalyticLowerBound h8).trans_le
          (qNeOneAnalyticLowerBound_le_sharp h8))
  · exact
      (qNeOneAnalyticLowerBound_gt_qNeOneCommonUpperBound_of_twelve (le_of_not_ge hu)).trans_le
        (qNeOneAnalyticLowerBound_le_sharp h8)

end PseudoPrime.LLS.Extensions
