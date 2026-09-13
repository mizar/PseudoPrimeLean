/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Analysis.LogarithmicRatios
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.Analysis.ElementaryBounds
import PseudoPrime.Analysis.LogarithmicMainTerms
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Numerical envelopes for the Q-ne-one extensions

These real-variable envelopes combine the LLS weighted-sum coefficients with the additional
conductor and parity corrections used in the Q-ne-one argument. The interval certificates and
the stronger even reciprocal remainder are extensions of the original Part 1 estimates.
General logarithmic ratios and the elementary logarithmic correction are imported from Analysis.
-/

namespace PseudoPrime.LLS.Extensions

/-!
The one-variable lower and upper expressions for the Q-ne-one even-character separation.
They are relaxed forms for the even-character analytic bounds: the lower expression replaces
`2 * log (2 * π) * log y` by `4 * log y`, while the upper expression uses `log π ≥ 1`
and discards the nonpositive even main-error term. The comparison is proved below for `y ≥ 8`.
-/

/-- The relaxed Q-ne-one lower envelope, with zero-mass and logarithmic losses explicit. -/
noncomputable def qNeOneLowerBound (y : ℝ) : ℝ :=
  y ^ 2 - (3 / 10 : ℝ) * (y + 1) - 4 * Real.log y - 1 - 2 * (Real.log y) ^ 2

/-- The relaxed even-character upper envelope used by `qNeOneLowerBound_gt_upperBound`. -/
noncomputable def qNeOneUpperBound (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
    (y - 1) * Real.log y

/-!
Input/assumptions: a real parameter `y`, later specialized to `log d`.
Definition: the retained even-character `Ẽ₀` contribution in the `c = 0`
upper bound.  The negative linear and quadratic logarithmic terms are kept
explicitly instead of being absorbed into the uniform constant `-11 / 4`.
Output: `1 / 2 - (log y) / 2 - 2 (log y)^2`.
Role: supplies the remainder term in `qNeOneAnalyticUpperBound`.
-/

noncomputable def qNeOneTildeE0UpperTerm (y : ℝ) : ℝ :=
  1 / 2 - 1 / 2 * Real.log y - 2 * (Real.log y) ^ 2

/-!
Input: a real radius parameter `y` for the even `c = 0` comparison.
Definition: the Riemann lower expression with zero-mass and common-factor losses.
Output: the candidate lower value `L(y)`.
Role: supplies the analytic lower envelope; it is definitionally equal to `qNeOneLowerBound`.
-/

noncomputable def qNeOneAnalyticLowerBound (y : ℝ) : ℝ :=
  y ^ 2 - (3 / 10 : ℝ) * (y + 1) - 4 * Real.log y - 1 - 2 * (Real.log y) ^ 2

/-!
Input: a real radius parameter `y` for the even `c = 0` comparison.
Definition: the candidate upper envelope obtained from the reciprocal zero-mass bound and
the retained `Ẽ₀` term.
Output: the candidate upper value `U(y)`.
Role: names a zero-mass-free comparison target; this definition asserts no analytic estimate.
-/

noncomputable def qNeOneAnalyticUpperBound (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) * (1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 8 / 5) +
    (y - 1 / 3) * Real.log y +
    qNeOneTildeE0UpperTerm y

/-!
Input/assumptions: the square-radius `c = 0` branch with the explicit `log 4` conductor penalty.
Definition: the B-free upper envelope obtained directly from the exact reciprocal bound and the
exact even main-error term, without spending the `log 4 - log π` contribution.
Output: an upper envelope retaining the exact even main-error term and reciprocal denominator.
Role: provides a valid intermediate envelope before any numerical simplification to the shorter
candidate `qNeOneAnalyticUpperBound`.
-/

noncomputable def qNeOneAnalyticUpperBoundLogFour (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) *
      (((1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 1 / 4 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2) +
    (1 / 2) * (y + Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
    (Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log (y ^ 2) -
      (1 / 2) * Real.log (y ^ 2) ^ 2)

/-!
The c=1 B-free upper envelope with the exact even main-error term and `log conductor ≤ y`.
-/

noncomputable def qNeOneAnalyticUpperBoundOne (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) * ((1 + 5 / (2 * y)) * (y / 2 - 2 * Real.log y + 1)) +
    (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
    (Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log (y ^ 2) -
      (1 / 2) * Real.log (y ^ 2) ^ 2)

/-!
Input/assumptions: the c=1 analytic envelope and `y ≥ 8`.
Conclusion: the exact c=1 envelope is bounded by `qNeOneUpperBound`.
Content: use `log π ≥ 1` and the nonpositive retained even main-error term.
Role: transfers `qNeOneLowerBound_gt_upperBound` to the exact c=1 envelope.
-/

theorem qNeOneAnalyticUpperBoundOne_le_qNeOneUpperBound {y : ℝ} (hy : 8 ≤ y) :
    qNeOneAnalyticUpperBoundOne y ≤ qNeOneUpperBound y := by
  have hypos : 0 < y := by linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogpi : 1 ≤ Real.log Real.pi := by
    have h3pi :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (3 : ℝ) by norm_num only)
        (show 0 < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
    linarith only [h3pi, Real.log_three_gt_d9]
  have hlogy_lower : 2 ≤ Real.log y := by
    have h8 :=
      Real.strictMonoOn_log.monotoneOn (show 0 < (8 : ℝ) by norm_num only) hypos
        (by linarith : (8 : ℝ) ≤ y)
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow] at h8
    norm_num only at h8 ⊢
    linarith only [h8, Real.log_two_gt_d9]
  have hpi : Real.pi ^ 2 / 24 ≤ (2 / 3 : ℝ) := by
    have hprod : 0 < (4 - Real.pi) * (4 + Real.pi) :=
      mul_pos (by linarith [Real.pi_lt_d4]) (by positivity)
    nlinarith only [hprod]
  have heuler : 0 ≤ Real.eulerMascheroniConstant :=
    le_trans (by norm_num only) (le_of_lt Real.one_half_lt_eulerMascheroniConstant)
  have hlogsq : 4 ≤ Real.log (y ^ 2) ^ 2 := by
    have hlogs : 4 ≤ Real.log (y ^ 2) := by
      rw [Real.log_pow]
      norm_num only
      linarith only [hlogy_lower]
    nlinarith only [hlogs, sq_nonneg (Real.log (y ^ 2) - 4)]
  have he :
    Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log (y ^ 2) -
        (1 / 2) * Real.log (y ^ 2) ^ 2 ≤
      0 := by
    have hlogs : 0 ≤ Real.log (y ^ 2) := by
      rw [Real.log_pow]
      norm_num only
      linarith only [hlogy]
    nlinarith only [hpi, heuler, hlogsq, mul_nonneg heuler hlogs]
  unfold qNeOneAnalyticUpperBoundOne qNeOneUpperBound
  have hlogpow : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [Real.log_pow]
    norm_num only
  rw [hlogpow]
  rw [hlogpow] at he
  nlinarith only [mul_le_mul_of_nonneg_right (sub_le_sub_left hlogpi y) hlogy, he]

/-- The `c = 0` reciprocal envelope `B₀*`, retaining the `log 4` penalty and `-4/5` error. -/
noncomputable def qNeOneBUpperBoundZeroStar (y : ℝ) : ℝ :=
  (((1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 4 / 5 -
      (2 * Real.log y - 8 / 5 - Real.log 2)) /
    (1 - 1 / y) ^ 2)

/-!
Input/assumptions: a radius `y ≥ 12`.
Conclusion: `B₀*` is bounded by a rationalized numerator while retaining its exact positive
denominator.
Content: use `log 4 - log π ≤ 39/100` and preserve the factor
`(1 - 1/y)^2` instead of replacing it by a constant.
Role: supplies the sharper y-dependent reciprocal input for the compact `[12,64]` certificate.
-/

theorem qNeOneBUpperBoundZeroStar_le_rationalized {y : ℝ} (hy : 12 ≤ y) :
    qNeOneBUpperBoundZeroStar y ≤
      (((1 / 2) * (1 - 1 / y ^ 2) * (y + 39 / 100) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2) := by
  have hypos : 0 < y := by linarith
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hp : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  have ha : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hi : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith only [hy]
    linarith
  have hlog4 : Real.log (4 : ℝ) ≤ (139 / 100 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_lt_d9]
  have hlogpi : 1 ≤ Real.log Real.pi := by
    have h3pi :=
      Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 3 by norm_num only)
        (show (0 : ℝ) < Real.pi by positivity) (le_of_lt Real.pi_gt_three)
    linarith only [h3pi, Real.log_three_gt_d9]
  apply (div_le_div_iff_of_pos_right hden).2
  have hnum :=
    mul_le_mul_of_nonneg_left (show y + Real.log 4 - Real.log Real.pi ≤ y + 39 / 100 by linarith) ha
  linarith only [hnum]

/-!
Input/assumptions: a radius `y ≥ 12`.
Conclusion: the reciprocal envelope has a sharper rationalized numerator with penalty `25/100`.
Content: use decimal lower and upper certificates for `log π` and `log 4`, while retaining the
positive denominator `(1 - 1/y)^2`.
Role: supplies the endpoint-tight input for the first compact interval of the bound.
-/

theorem qNeOneBUpperBoundZeroStar_le_rationalized_sharp {y : ℝ} (hy : 12 ≤ y) :
    qNeOneBUpperBoundZeroStar y ≤
      (((1 / 2) * (1 - 1 / y ^ 2) * (y + 25 / 100) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - Real.log 2)) /
        (1 - 1 / y) ^ 2) := by
  have hypos : 0 < y := by linarith
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hp : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith only [hy]
    positivity
  have ha : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
    have hi : 1 / y ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
      nlinarith only [hy, sq_nonneg (y - 1)]
    linarith only [hi]
  have hlog4 : Real.log (4 : ℝ) ≤ (139 : ℝ) / 100 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_lt_d9]
  have hlogpi : (114 : ℝ) / 100 < Real.log Real.pi := by
    have hpi : (314 : ℝ) / 100 < Real.pi := by
      have h := Real.pi_gt_d2
      norm_num only at h ⊢
      exact h
    have hx : (7 : ℝ) / 150 < Real.pi / 3 - 1 := by nlinarith only [hpi]
    have hxpos : 0 < Real.pi / 3 - 1 := by linarith
    have hlogadd := Real.lt_log_one_add_of_pos hxpos
    have hlogdiv : Real.log (Real.pi / 3) = Real.log Real.pi - Real.log 3 := by
      rw [Real.log_div (by positivity) (by norm_num only)]
    have hlogone : Real.log (1 + (Real.pi / 3 - 1)) = Real.log (Real.pi / 3) := by
      congr 1
      ring
    rw [hlogone, hlogdiv] at hlogadd
    have hfrac : (9 : ℝ) / 200 < 2 * (Real.pi / 3 - 1) / (Real.pi / 3 - 1 + 2) := by
      apply (lt_div_iff₀ (by linarith)).2
      linarith only [hx]
    linarith only [hlogadd, hfrac, Real.log_three_gt_d9]
  apply (div_le_div_iff_of_pos_right hden).2
  have hnum :=
    mul_le_mul_of_nonneg_left (show y + Real.log 4 - Real.log Real.pi ≤ y + 25 / 100 by linarith) ha
  linarith only [hnum]

/-- A nonnegative cleared numerator bounds `B₀*` by `y/2 - 2 log y + C` for `y ≥ 12`. -/
theorem qNeOneBUpperBoundZeroStar_le_affine_of_cleared {y C : ℝ} (hy : 12 ≤ y)
    (hnum :
      0 ≤
        160 * Real.log y * y - 80 * Real.log y - 40 * Real.log 2 * y ^ 2 + 7 * y ^ 2 - 128 * y +
          89 +
          40 * (C - 21 / 10) * (y - 1) ^ 2) :
    qNeOneBUpperBoundZeroStar y ≤ y / 2 - 2 * Real.log y + C := by
  have hy0 : 0 < y := by linarith only [hy]
  have hB := qNeOneBUpperBoundZeroStar_le_rationalized_sharp hy
  have hid :
    (y / 2 - 2 * Real.log y + C) -
        (((1 / 2) * (1 - 1 / y ^ 2) * (y + 25 / 100) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2) =
      (160 * Real.log y * y - 80 * Real.log y - 40 * Real.log 2 * y ^ 2 + 7 * y ^ 2 - 128 * y + 89 +
          40 * (C - 21 / 10) * (y - 1) ^ 2) /
        (40 * (y - 1) ^ 2) := by
    have hym : y - 1 ≠ 0 := by linarith only [hy]
    field_simp [ne_of_gt hy0, hym]
    ring
  have hden' : 0 < 40 * (y - 1) ^ 2 := by
    have : 0 < y - 1 := by linarith only [hy]
    positivity
  have hfrac :
    0 ≤
      (160 * Real.log y * y - 80 * Real.log y - 40 * Real.log 2 * y ^ 2 + 7 * y ^ 2 - 128 * y + 89 +
          40 * (C - 21 / 10) * (y - 1) ^ 2) /
        (40 * (y - 1) ^ 2) :=
    div_nonneg hnum (le_of_lt hden')
  have hdiff :
    0 ≤
      (y / 2 - 2 * Real.log y + C) -
        (((1 / 2) * (1 - 1 / y ^ 2) * (y + 25 / 100) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2) := by
    rw [hid]
    exact hfrac
  exact hB.trans (sub_nonneg.mp hdiff)

/-!
Input/assumptions: `12 ≤ y ≤ 13`.
Conclusion: the sharper rationalized reciprocal bound closes with the explicit
constant `21/10` in the affine form needed by the first compact interval.
Content: use the chord lower bound for `log y` obtained from
`Real.le_log_one_add_of_nonneg` at the anchor `12`, then clear the positive
denominators.  The remaining polynomial is nonnegative on the interval.
Role: records the first interval certificate for the reciprocal-envelope
table; later intervals use the same cleared-denominator pattern with their own
anchor and constant.
-/

theorem qNeOneBUpperBoundZeroStar_le_affine_twelve_thirteen {y : ℝ} (hy : 12 ≤ y) (hy13 : y ≤ 13) :
    qNeOneBUpperBoundZeroStar y ≤ y / 2 - 2 * Real.log y + 21 / 10 := by
  have hy0 : 0 < y := by linarith
  have hlog : (247 : ℝ) / 100 + (2 / 25) * (y - 12) < Real.log y := by
    have hlog12 : (247 : ℝ) / 100 < Real.log 12 := by
      rw [show (12 : ℝ) = 3 * 4 by norm_num only,
        Real.log_mul (by norm_num only) (by norm_num only), Real.log_four_eq]
      linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
    have hfactor : (12 : ℝ) * (y / 12) = y := by field_simp
    rw [← hfactor, Real.log_mul (by norm_num only) (by positivity)]
    have hx : 0 ≤ y / 12 - 1 := by linarith
    have hla := Real.le_log_one_add_of_nonneg hx
    have hla' : 2 * (y / 12 - 1) / ((y / 12 - 1) + 2) ≤ Real.log (y / 12) := by
      convert hla using 1
      all_goals ring_nf
    have hfrac : (2 / 25 : ℝ) * (y - 12) ≤ 2 * (y / 12 - 1) / ((y / 12 - 1) + 2) := by
      have hden : 0 < (y / 12 - 1) + 2 := by linarith
      apply (le_div_iff₀ hden).2
      nlinarith only [mul_nonneg (by linarith : 0 ≤ y - 12) (by linarith : 0 ≤ 13 - y)]
    linarith only [hlog12, hla', hfrac, hfactor]
  have hlog2 : Real.log 2 ≤ (347 : ℝ) / 500 := by linarith [Real.log_two_lt_d9]
  have hB := qNeOneBUpperBoundZeroStar_le_rationalized_sharp hy
  have hnum :
    0 ≤
      160 * Real.log y * y - 80 * Real.log y - 40 * Real.log 2 * y ^ 2 + 7 * y ^ 2 - 128 * y +
        89 := by
    have hc : 0 ≤ 160 * y - 80 := by linarith only [hy]
    have hL := mul_le_mul_of_nonneg_right (le_of_lt hlog) hc
    have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ 40 * y ^ 2)
    nlinarith only [hL, h2, sq_nonneg (y - 12), sq_nonneg (y - 13), hy, hy13]
  have hid :
    (y / 2 - 2 * Real.log y + 21 / 10) -
        (((1 / 2) * (1 - 1 / y ^ 2) * (y + 25 / 100) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2) =
      (160 * Real.log y * y - 80 * Real.log y - 40 * Real.log 2 * y ^ 2 + 7 * y ^ 2 - 128 * y +
          89) /
        (40 * (y - 1) ^ 2) := by
    have hym : y - 1 ≠ 0 := by linarith only [hy]
    field_simp [ne_of_gt hy0, hym]
    ring
  have hden' : 0 < 40 * (y - 1) ^ 2 := by
    have : 0 < y - 1 := by linarith only [hy]
    positivity
  have hfrac :
    0 ≤
      (160 * Real.log y * y - 80 * Real.log y - 40 * Real.log 2 * y ^ 2 + 7 * y ^ 2 - 128 * y +
          89) /
        (40 * (y - 1) ^ 2) :=
    div_nonneg hnum (le_of_lt hden')
  have hdiff :
    0 ≤
      (y / 2 - 2 * Real.log y + 21 / 10) -
        (((1 / 2) * (1 - 1 / y ^ 2) * (y + 25 / 100) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) /
          (1 - 1 / y) ^ 2) := by
    rw [hid]
    exact hfrac
  linarith only [hB, hdiff]

/-! The second compact interval closes with the rational constant `11/5`. -/

theorem qNeOneBUpperBoundZeroStar_le_affine_thirteen_sixteen {y : ℝ} (hy : 13 ≤ y) (hy16 : y ≤ 16) :
    qNeOneBUpperBoundZeroStar y ≤ y / 2 - 2 * Real.log y + 11 / 5 := by
  have hlog13 : (256 : ℝ) / 100 < Real.log 13 := by
    have h12 : (248 : ℝ) / 100 < Real.log 12 := by
      rw [show (12 : ℝ) = 3 * 4 by norm_num only,
        Real.log_mul (by norm_num only) (by norm_num only), Real.log_four_eq]
      linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
    have hfac : (12 : ℝ) * (13 / 12) = 13 := by norm_num only
    rw [← hfac, Real.log_mul (by norm_num only) (by norm_num only)]
    have hla := Real.le_log_one_add_of_nonneg (x := (1 / 12 : ℝ)) (by norm_num only)
    norm_num only at hla
    linarith only [h12, hla]
  have hlog :=
    Analysis.log_gt_affine_of_anchor (a := (13 : ℝ)) (b := 16) (y := y) (L := 256 / 100)
      (by norm_num only) (by norm_num only) hy hy16 hlog13
  have hlog2 : Real.log 2 ≤ (347 : ℝ) / 500 := by linarith [Real.log_two_lt_d9]
  apply qNeOneBUpperBoundZeroStar_le_affine_of_cleared (by linarith)
  have hc : 0 ≤ 160 * y - 80 := by linarith only [hy]
  have hL := mul_le_mul_of_nonneg_right (le_of_lt hlog) hc
  have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ 40 * y ^ 2)
  nlinarith only [hL, h2, sq_nonneg (y - 13), sq_nonneg (y - 16), hy, hy16]

/-! The third compact interval closes with the rational constant `23/10`. -/

theorem qNeOneBUpperBoundZeroStar_le_affine_sixteen_twenty_four {y : ℝ} (hy : 16 ≤ y)
    (hy24 : y ≤ 24) : qNeOneBUpperBoundZeroStar y ≤ y / 2 - 2 * Real.log y + 23 / 10 := by
  have hlog16 : (277 : ℝ) / 100 < Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9]
  have hlog :=
    Analysis.log_gt_affine_of_anchor (a := (16 : ℝ)) (b := 24) (y := y) (L := 277 / 100)
      (by norm_num only) (by norm_num only) hy hy24 hlog16
  have hlog2 : Real.log 2 ≤ (347 : ℝ) / 500 := by linarith [Real.log_two_lt_d9]
  apply qNeOneBUpperBoundZeroStar_le_affine_of_cleared (by linarith)
  have hc : 0 ≤ 160 * y - 80 := by linarith only [hy]
  have hL := mul_le_mul_of_nonneg_right (le_of_lt hlog) hc
  have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ 40 * y ^ 2)
  nlinarith only [hL, h2, sq_nonneg (y - 16), sq_nonneg (y - 24), hy, hy24]

/-! The fourth compact interval closes with the rational constant `12/5`. -/

theorem qNeOneBUpperBoundZeroStar_le_affine_twenty_four_thirty_two {y : ℝ} (hy : 24 ≤ y)
    (hy32 : y ≤ 32) : qNeOneBUpperBoundZeroStar y ≤ y / 2 - 2 * Real.log y + 12 / 5 := by
  have hlog24 : (317 : ℝ) / 100 < Real.log 24 := by
    rw [show (24 : ℝ) = 3 * 2 ^ 3 by norm_num only,
      Real.log_mul (by norm_num only) (by norm_num only), Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hlog :=
    Analysis.log_gt_affine_of_anchor (a := (24 : ℝ)) (b := 32) (y := y) (L := 317 / 100)
      (by norm_num only) (by norm_num only) hy hy32 hlog24
  have hlog2 : Real.log 2 ≤ (347 : ℝ) / 500 := by linarith [Real.log_two_lt_d9]
  apply qNeOneBUpperBoundZeroStar_le_affine_of_cleared (by linarith)
  have hc : 0 ≤ 160 * y - 80 := by linarith only [hy]
  have hL := mul_le_mul_of_nonneg_right (le_of_lt hlog) hc
  have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ 40 * y ^ 2)
  nlinarith only [hL, h2, sq_nonneg (y - 24), sq_nonneg (y - 32), hy, hy32]

/-! The fifth compact interval closes with the same rational constant `12/5`. -/

theorem qNeOneBUpperBoundZeroStar_le_affine_thirty_two_forty_eight {y : ℝ} (hy : 32 ≤ y)
    (hy48 : y ≤ 48) : qNeOneBUpperBoundZeroStar y ≤ y / 2 - 2 * Real.log y + 12 / 5 := by
  have hlog32 : (346 : ℝ) / 100 < Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9]
  have hlog :=
    Analysis.log_gt_affine_of_anchor (a := (32 : ℝ)) (b := 48) (y := y) (L := 346 / 100)
      (by norm_num only) (by norm_num only) hy hy48 hlog32
  have hlog2 : Real.log 2 ≤ (347 : ℝ) / 500 := by linarith [Real.log_two_lt_d9]
  apply qNeOneBUpperBoundZeroStar_le_affine_of_cleared (by linarith)
  have hc : 0 ≤ 160 * y - 80 := by linarith only [hy]
  have hL := mul_le_mul_of_nonneg_right (le_of_lt hlog) hc
  have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : (0 : ℝ) ≤ 40 * y ^ 2)
  nlinarith only [hL, h2, sq_nonneg (y - 32), sq_nonneg (y - 48), hy, hy48]

/-!
Input/assumptions: a radius `y ≥ 12`.
Conclusion: the exact c=0 reciprocal envelope is at most `y + 3`.
Content: combine the rationalized numerator with the positive denominator lower bound
`(11/12)^2 ≤ (1 - 1/y)^2`.
Role: supplies a coarse estimate alongside the sharper compact-interval certificates.
-/

theorem qNeOneBUpperBoundZeroStar_le_linear {y : ℝ} (hy : 12 ≤ y) :
    qNeOneBUpperBoundZeroStar y ≤ y + 3 := by
  have hypos : 0 < y := by linarith
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hp : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  have hdenlb : (11 / 12 : ℝ) ^ 2 ≤ (1 - 1 / y) ^ 2 := by
    have h : (1 / y : ℝ) ≤ 1 / 12 := by
      apply (div_le_iff₀ hypos).2
      linarith
    nlinarith only [h, sq_nonneg ((1 - 1 / y) - 11 / 12)]
  have hlog2hi : Real.log 2 < (7 : ℝ) / 10 := by
    have h := Real.log_two_lt_d9
    norm_num only at h ⊢
    linarith
  have hlogylo : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  unfold qNeOneBUpperBoundZeroStar
  apply (div_le_iff₀ hden).2
  have hinv : 0 ≤ 1 / y ^ 2 := by positivity
  have hinvle : 1 / y ^ 2 ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
    nlinarith only [hy]
  have hfactor : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by linarith only [hinvle]
  have hupperfactor : (1 / 2 : ℝ) * (1 - 1 / y ^ 2) ≤ 1 / 2 := by nlinarith only [hinv]
  have hmain : (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (y + 39 / 100) ≤ y / 2 + 39 / 200 := by
    have hp : 0 ≤ y + 39 / 100 := by positivity
    have h := mul_le_mul_of_nonneg_right hupperfactor hp
    nlinarith only [h]
  have hnum :
    (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - Real.log 2) ≤
      y / 2 + 39 / 200 + 3 / 2 := by
    have ha : Real.log 4 - Real.log Real.pi ≤ 39 / 100 := by
      linarith [show Real.log 4 ≤ (139 : ℝ) / 100
          by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
          norm_num only
          linarith [Real.log_two_lt_d9],
        show (1 : ℝ) ≤ Real.log Real.pi
          by
          have h :=
            Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < 3 by norm_num only) Real.pi_pos
              (le_of_lt Real.pi_gt_three)
          linarith [Real.log_three_gt_d9]]
    have hp : 0 ≤ y + Real.log 4 - Real.log Real.pi := by
      linarith [Analysis.log_four_sub_log_pi_pos]
    have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_left ha y) hfactor
    nlinarith only [hmain, hmul, hlog2hi, hlogylo]
  have htarget : y / 2 + 39 / 200 + 3 / 2 ≤ (y + 3) * (11 / 12 : ℝ) ^ 2 := by nlinarith only [hy]
  have hscale : 0 ≤ (y + 3) * ((1 - 1 / y) ^ 2 - (11 / 12 : ℝ) ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hdenlb)
  nlinarith only [hmain, hnum, htarget, hscale]

/-- The `c = -1` reciprocal envelope `B₋*`, with correction `(4/3) log 2` and error `-4/5`. -/
noncomputable def qNeOneBUpperBoundNegOneStar (y : ℝ) : ℝ :=
  (((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
      (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
    (1 - 1 / y) ^ 2)

/-!
The reciprocal envelopes differ by `log 2 * (2/3 - 1/y²) / (1 - 1/y)²`.
The identity is algebraic; positivity is supplied separately for `y ≥ 8`.
-/

theorem qNeOneBUpperBoundZeroStar_sub_negOneStar_eq {y : ℝ} (hy : 8 ≤ y) :
    qNeOneBUpperBoundZeroStar y - qNeOneBUpperBoundNegOneStar y =
      Real.log 2 * (2 / 3 - 1 / y ^ 2) / (1 - 1 / y) ^ 2 := by
  have hypos : 0 < y := by linarith
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only
  have hden : (1 - 1 / y) ^ 2 ≠ 0 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  unfold qNeOneBUpperBoundZeroStar qNeOneBUpperBoundNegOneStar
  rw [hlog4]
  field_simp [hden]
  ring

/-! The explicit c=-1 lower envelope, retaining the odd-tail square-log loss. -/

noncomputable def qNeOneAnalyticLowerBoundNegOne (y : ℝ) : ℝ :=
  y ^ 2 - Real.log (2 * Real.pi) * (2 * Real.log y) - 1 -
    2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (y + 1) -
    (3 / 2) * (2 * Real.log y) ^ 2

/-!
The c=-1 B-free upper envelope with `log conductor ≤ y - log 4`, before numerical relaxation.
-/

noncomputable def qNeOneAnalyticUpperBoundNegOneLogFour (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) *
      (((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log 4 - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
        (1 - 1 / y) ^ 2) +
    (1 / 2) * (y - Real.log 4 - Real.log Real.pi) * (2 * Real.log y) +
    (Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log (y ^ 2) -
      (1 / 2) * Real.log (y ^ 2) ^ 2)

/-!
The c=-1 B-free upper envelope with `log conductor ≤ y`, before correction comparison.
-/

noncomputable def qNeOneAnalyticUpperBoundNegOne (y : ℝ) : ℝ :=
  (2 * y + 2 + 2 * Real.log y) *
      (((1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log Real.pi) - 4 / 5 -
          (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) /
        (1 - 1 / y) ^ 2) +
    (1 / 2) * (y - Real.log Real.pi) * (2 * Real.log y) +
    (Real.pi ^ 2 / 24 - (Real.eulerMascheroniConstant / 2) * Real.log (y ^ 2) -
      (1 / 2) * Real.log (y ^ 2) ^ 2)

/-!
The c=-1 exact upper envelope is no larger than the c=0 `log 4` envelope for `y ≥ 8`.
The comparison keeps the reciprocal numerators and conductor terms explicit.
-/

theorem qNeOneAnalyticUpperBoundNegOneLogFour_le {y : ℝ} (hy : 8 ≤ y) :
    qNeOneAnalyticUpperBoundNegOneLogFour y ≤ qNeOneAnalyticUpperBoundLogFour y := by
  have hypos : 0 < y := by linarith
  have hden : 0 < (1 - 1 / y) ^ 2 := by
    have hpos : 0 < 1 - 1 / y := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hypos).2
      linarith
    positivity
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hlog2upper : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow]
    norm_num only
  have hnum :
    (1 / 2) * (1 - 1 / y ^ 2) * (y - Real.log 4 - Real.log Real.pi) - 4 / 5 -
        (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2) ≤
      (1 / 2) * (1 - 1 / y ^ 2) * (y + Real.log 4 - Real.log Real.pi) - 1 / 4 -
        (2 * Real.log y - 8 / 5 - Real.log 2) := by
    rw [hlog4]
    have hfactor : 0 ≤ (1 / 2 : ℝ) * (1 - 1 / y ^ 2) := by
      have hy2 : 1 ≤ y ^ 2 := by nlinarith only [hy]
      have hinv : 1 / y ^ 2 ≤ 1 := by
        apply (div_le_iff₀ (sq_pos_of_pos hypos)).2
        nlinarith only [hy2]
      linarith
    have hfactorlog : 0 ≤ ((1 / 2 : ℝ) * (1 - 1 / y ^ 2)) * Real.log 2 :=
      mul_nonneg hfactor hlog2.le
    have hid :
      ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (y + 2 * Real.log 2 - Real.log Real.pi) - 1 / 4 -
            (2 * Real.log y - 8 / 5 - Real.log 2)) -
          ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (y - 2 * Real.log 2 - Real.log Real.pi) - 4 / 5 -
            (2 * Real.log y - 8 / 5 - (4 / 3) * Real.log 2)) =
        4 * ((1 / 2 : ℝ) * (1 - 1 / y ^ 2)) * Real.log 2 + 11 / 20 - (1 / 3 : ℝ) * Real.log 2 := by
      ring
    have hterm : 0 ≤ 4 * ((1 / 2 : ℝ) * (1 - 1 / y ^ 2)) * Real.log 2 :=
      mul_nonneg (mul_nonneg (by norm_num only) hfactor) hlog2.le
    have hscaled : (1 / 3 : ℝ) * Real.log 2 ≤ 7 / 30 := by
      exact (mul_le_mul_of_nonneg_left hlog2upper (by norm_num only)).trans_eq (by norm_num only)
    have hrem : 0 ≤ (11 / 20 : ℝ) - (1 / 3) * Real.log 2 :=
      sub_nonneg.mpr (hscaled.trans (by norm_num only))
    have hdiff :
      0 ≤
        4 * ((1 / 2 : ℝ) * (1 - 1 / y ^ 2)) * Real.log 2 + 11 / 20 - (1 / 3 : ℝ) * Real.log 2 := by
      calc
        0 ≤
            4 * ((1 / 2 : ℝ) * (1 - 1 / y ^ 2)) * Real.log 2 +
              (11 / 20 - (1 / 3 : ℝ) * Real.log 2) :=
          add_nonneg hterm hrem
        _ = 4 * ((1 / 2 : ℝ) * (1 - 1 / y ^ 2)) * Real.log 2 + 11 / 20 - (1 / 3 : ℝ) * Real.log 2 :=
          by ring
    rw [← hid] at hdiff
    exact sub_nonneg.mp hdiff
  have hfrac := (div_le_div_iff_of_pos_right hden).2 hnum
  have hcoef : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith
  have hmul := mul_le_mul_of_nonneg_left hfrac hcoef
  unfold qNeOneAnalyticUpperBoundNegOneLogFour qNeOneAnalyticUpperBoundLogFour
  nlinarith only [hmul, mul_nonneg hlogy (by positivity : (0 : ℝ) ≤ Real.log 4)]

/-- The analytic lower envelope is definitionally equal to `qNeOneLowerBound`. -/
theorem qNeOneAnalyticLowerBound_eq_qNeOneLowerBound (y : ℝ) :
    qNeOneAnalyticLowerBound y = qNeOneLowerBound y := by rfl

/-- The retained `Ẽ₀` contribution is no larger than its constant part for `y ≥ 1`. -/
theorem qNeOneTildeE0UpperTerm_le_half {y : ℝ} (hy : 1 ≤ y) : qNeOneTildeE0UpperTerm y ≤ 1 / 2 := by
  rw [qNeOneTildeE0UpperTerm]
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  linarith only [hlog, sq_nonneg (Real.log y)]

/-!
The two-interval numerical separation for the Q-ne-one radius.
For `8 ≤ y ≤ 20`, log concavity gives the chord lower bound
`log y ≥ 2 + (y - 8) / 18`; for `20 ≤ y`, `log y ≥ 11 / 3 - 20 / y` follows from
`log (20 / y) ≤ 20 / y - 1`.  Both substitutions reduce the margin to positive rational
polynomials.
-/

theorem qNeOneLowerBound_gt_upperBound {y : ℝ} (hy : 8 ≤ y) :
    qNeOneUpperBound y < qNeOneLowerBound y := by
  have hypos : 0 < y := by linarith
  have hmargin :
    0 <
      (2 + 10 / y) * (Real.log y) ^ 2 + (2 * y + 13 / 2 + 5 / y) * Real.log y - 29 / 5 * y -
        54 / 5 -
        5 / y := by
    by_cases hy20 : y ≤ 20
    · have hlog : 2 + (y - 8) / 18 ≤ Real.log y := by
        let a : ℝ := (20 - y) / 12
        let b : ℝ := (y - 8) / 12
        have ha : 0 ≤ a := by
          dsimp [a]; positivity
        have hb : 0 ≤ b := by
          dsimp [b]; positivity
        have hab : a + b = 1 := by
          dsimp [a, b]; ring
        have hcomb : a * 8 + b * 20 = y := by
          dsimp [a, b]; ring
        have hconc :=
          strictConcaveOn_log_Ioi.concaveOn.2 (show 0 < (8 : ℝ) by norm_num only)
            (show 0 < (20 : ℝ) by norm_num only) ha hb hab
        have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
          norm_num only
          linarith [Real.log_two_gt_d9]
        have hlog20 : (8 / 3 : ℝ) ≤ Real.log 20 := by
          have h16 : Real.log 16 ≤ Real.log 20 := by
            apply Real.strictMonoOn_log.monotoneOn <;> norm_num only [Set.mem_Ioi]
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow] at h16
          norm_num only at h16 ⊢
          have h2 : (2 / 3 : ℝ) ≤ Real.log 2 := le_trans (by norm_num only) Real.log_two_gt_d9.le
          have hscaled := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 4 by norm_num only)
          have htarget : (8 / 3 : ℝ) ≤ 4 * Real.log 2 := by
            norm_num only at hscaled ⊢
            exact hscaled
          exact htarget.trans h16
        have hconc' : a * Real.log 8 + b * Real.log 20 ≤ Real.log y := by
          simpa only [smul_eq_mul, hcomb] using hconc
        calc
          2 + (y - 8) / 18 = a * 2 + b * (8 / 3) := by
            dsimp [a, b]; ring
          _ ≤ a * Real.log 8 + b * Real.log 20 := by gcongr
          _ ≤ Real.log y := hconc'
      have hc1 : 0 ≤ 2 + 10 / y := by positivity
      have hc2 : 0 ≤ 2 * y + 13 / 2 + 5 / y := by positivity
      have hl0 : 0 ≤ 2 + (y - 8) / 18 := by positivity
      have hlog_nonneg : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
      have hsquares : (2 + (y - 8) / 18) ^ 2 ≤ (Real.log y) ^ 2 :=
        (sq_le_sq₀ hl0 hlog_nonneg).2 hlog
      have hmono :
        (2 + 10 / y) * (2 + (y - 8) / 18) ^ 2 + (2 * y + 13 / 2 + 5 / y) * (2 + (y - 8) / 18) -
            29 / 5 * y -
            54 / 5 -
            5 / y ≤
          (2 + 10 / y) * (Real.log y) ^ 2 + (2 * y + 13 / 2 + 5 / y) * Real.log y - 29 / 5 * y -
            54 / 5 -
            5 / y := by
        have hsqmul := mul_le_mul_of_nonneg_left hsquares hc1
        have hlinmul := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hlog) hc2
        linarith
      have hquad : 0 < 1399 * (y - 8) ^ 2 - 4122 * (y - 8) + 18468 := by
        have hsquare : 0 ≤ (1399 * (y - 8) - 2061) ^ 2 := sq_nonneg _
        have hscaled : 0 < (4 * 1399 : ℝ) * (1399 * (y - 8) ^ 2 - 4122 * (y - 8) + 18468) := by
          calc
            (0 : ℝ) < 4 * (1399 * (y - 8) - 2061) ^ 2 + 86356044 := by
              exact
                add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num only) hsquare) (by norm_num only)
            _ = (4 * 1399 : ℝ) * (1399 * (y - 8) ^ 2 - 4122 * (y - 8) + 18468) := by ring
        have hmul :
          (4 * 1399 : ℝ) * 0 < (4 * 1399 : ℝ) * (1399 * (y - 8) ^ 2 - 4122 * (y - 8) + 18468) := by
          simpa only [mul_zero, Nat.ofNat_pos, mul_pos_iff_of_pos_left] using hscaled
        exact lt_of_mul_lt_mul_left hmul (by norm_num only)
      have ht3 : 0 ≤ 190 * (y - 8) ^ 3 := by positivity
      have hnum : 0 < 190 * y ^ 3 - 3161 * y ^ 2 + 9974 * y + 43700 := by
        nlinarith only [hquad, ht3]
      have hpoly :
        0 <
          (2 + 10 / y) * (2 + (y - 8) / 18) ^ 2 + (2 * y + 13 / 2 + 5 / y) * (2 + (y - 8) / 18) -
            29 / 5 * y -
            54 / 5 -
            5 / y := by
        field_simp
        nlinarith only [hnum]
      linarith
    · have hy20' : 20 ≤ y := le_of_not_ge hy20
      have hlog20 : (8 / 3 : ℝ) ≤ Real.log 20 := by
        have h16 : Real.log 16 ≤ Real.log 20 := by
          apply Real.strictMonoOn_log.monotoneOn <;> norm_num only [Set.mem_Ioi]
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow] at h16
        norm_num only at h16 ⊢
        linarith only [h16, Real.log_two_gt_d9]
      have hquot : 0 < 20 / y := by positivity
      have hlogquot := Real.log_le_sub_one_of_pos hquot
      have hlogdiv : Real.log (y / 20) = -Real.log (20 / y) := by
        rw [Real.log_div (ne_of_gt hypos) (by norm_num only : (20 : ℝ) ≠ 0)]
        rw [Real.log_div (by norm_num only : (20 : ℝ) ≠ 0) hypos.ne']
        ring
      have hlog20y : Real.log 20 + Real.log (y / 20) = Real.log y := by
        rw [Real.log_div hypos.ne' (by norm_num only : (20 : ℝ) ≠ 0)]
        ring
      have hlog : 11 / 3 - 20 / y ≤ Real.log y := by
        rw [← hlog20y, hlogdiv]
        linarith
      have hl0 : 0 ≤ 11 / 3 - 20 / y := by
        apply sub_nonneg.mpr
        apply (div_le_iff₀ hypos).2
        linarith
      have hlog_nonneg : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
      have hsquares : (11 / 3 - 20 / y) ^ 2 ≤ (Real.log y) ^ 2 := (sq_le_sq₀ hl0 hlog_nonneg).2 hlog
      have hc1 : 0 ≤ 2 + 10 / y := by positivity
      have hc2 : 0 ≤ 2 * y + 13 / 2 + 5 / y := by positivity
      have hmono :
        (2 + 10 / y) * (11 / 3 - 20 / y) ^ 2 + (2 * y + 13 / 2 + 5 / y) * (11 / 3 - 20 / y) -
            29 / 5 * y -
            54 / 5 -
            5 / y ≤
          (2 + 10 / y) * (Real.log y) ^ 2 + (2 * y + 13 / 2 + 5 / y) * Real.log y - 29 / 5 * y -
            54 / 5 -
            5 / y := by
        have hsqmul := mul_le_mul_of_nonneg_left hsquares hc1
        have hlinmul := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hlog) hc2
        linarith
      have heq :
        (2 + 10 / y) * (11 / 3 - 20 / y) ^ 2 + (2 * y + 13 / 2 + 5 / y) * (11 / 3 - 20 / y) -
            29 / 5 * y -
            54 / 5 -
            5 / y =
          23 / 15 * y - 7 / 90 - 2480 / (9 * y) - 2300 / (3 * y ^ 2) + 4000 / y ^ 3 := by
        field_simp
        ring
      rw [heq] at hmono
      have h1 : 2480 / (9 * y) ≤ 124 / 9 := by
        apply (div_le_iff₀ (by positivity : 0 < 9 * y)).2
        calc
          (2480 : ℝ) = 124 * 20 := by norm_num only
          _ ≤ 124 * y := mul_le_mul_of_nonneg_left hy20' (by norm_num only)
          _ = 124 / 9 * (9 * y) := by ring
      have h2 : 2300 / (3 * y ^ 2) ≤ 23 / 12 := by
        apply (div_le_iff₀ (by positivity : 0 < 3 * y ^ 2)).2
        have hy2 : (400 : ℝ) ≤ y ^ 2 := by
          calc
            (400 : ℝ) = 20 * 20 := by norm_num only
            _ ≤ y * y := mul_le_mul hy20' hy20' (by norm_num only) hypos.le
            _ = y ^ 2 := by ring
        calc
          (2300 : ℝ) = (23 / 4) * 400 := by norm_num only
          _ ≤ (23 / 4) * y ^ 2 := mul_le_mul_of_nonneg_left hy2 (by norm_num only)
          _ = 23 / 12 * (3 * y ^ 2) := by ring
      have hconst : 0 < (92 / 3 : ℝ) - 7 / 90 - 124 / 9 - 23 / 12 := by norm_num only
      have hyterm : (92 / 3 : ℝ) ≤ 23 / 15 * y := by
        calc
          (92 / 3 : ℝ) = 23 / 15 * 20 := by norm_num only
          _ ≤ 23 / 15 * y := mul_le_mul_of_nonneg_left hy20' (by norm_num only)
      have hpos : 0 ≤ 4000 / y ^ 3 := by positivity
      have hpoly :
        0 < 23 / 15 * y - 7 / 90 - 2480 / (9 * y) - 2300 / (3 * y ^ 2) + 4000 / y ^ 3 := by
        linarith only [hconst, hyterm, h1, h2, hpos]
      exact hpoly.trans_le hmono
  have hidentity :
    qNeOneLowerBound y - qNeOneUpperBound y =
      (2 + 10 / y) * (Real.log y) ^ 2 + (2 * y + 13 / 2 + 5 / y) * Real.log y - 29 / 5 * y -
        54 / 5 -
        5 / y := by
    dsimp [qNeOneLowerBound, qNeOneUpperBound]
    field_simp
    ring
  have hdiff : 0 < qNeOneLowerBound y - qNeOneUpperBound y := by
    rw [hidentity]
    exact hmargin
  exact sub_pos.mp hdiff

/-! The c=1 analytic envelope is strictly below the common lower envelope on `y ≥ 8`. -/

theorem qNeOneAnalyticUpperBoundOne_lt_qNeOneAnalyticLowerBound {y : ℝ} (hy : 8 ≤ y) :
    qNeOneAnalyticUpperBoundOne y < qNeOneAnalyticLowerBound y := by
  exact
    (qNeOneAnalyticUpperBoundOne_le_qNeOneUpperBound hy).trans_lt
      (qNeOneLowerBound_gt_upperBound hy)

/--
Input/assumptions: `x ≥ 64`.
Conclusion: the even reciprocal main-error term is strictly below `-4/5`.
Content: use the monotone logarithmic ratio from Analysis, the decimal logarithm bounds, and
`γ > 27/50` with the larger margin required by the Q-ne-one B estimate.
Role: the strong even remainder consumed by the quadratic reciprocal raw-formula adapter.
-/
theorem llsPrimitiveReciprocalEvenMainError_lt_neg_four_fifths {x : ℝ} (hx : 64 ≤ x) :
    Analysis.primitiveReciprocalEvenMainError x < -(4 / 5 : ℝ) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hratio_le : (Real.log x + 1) / x ≤ Analysis.logLinearRatio x := by
    unfold Analysis.logLinearRatio
    apply div_le_div_of_nonneg_right _ hxpos.le
    linarith
  have hratio_anti :
    Analysis.logLinearRatio x ≤ Analysis.logLinearRatio 64 :=
    Analysis.strictAntiOn_logLinearRatio.antitoneOn
      (by
        simp only [Set.mem_Ici]; norm_num only)
      (by
        simp only [Set.mem_Ici]; linarith)
      hx
  have hratio64 : Analysis.logLinearRatio 64 = (12 * Real.log 2 + 1) / 64 := by
    unfold Analysis.logLinearRatio
    rw [show (64 : ℝ) = 2 ^ 6 from by norm_num only, Real.log_pow]
    norm_num only
    ring
  have hγ := Analysis.twenty_seven_fiftieths_lt_eulerMascheroniConstant
  have hlog2lo := Real.log_two_gt_d9
  have hlog2hi := Real.log_two_lt_d9
  have hinv_le : 1 / x ≤ 1 / 64 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hx
  have h1mx_ge : (63 / 64 : ℝ) ≤ 1 - 1 / x := by linarith
  have h1mx_nn : (0 : ℝ) ≤ 1 - 1 / x := by linarith
  have hterm1 : (27 / 100 : ℝ) * (63 / 64) ≤ (Real.eulerMascheroniConstant / 2) * (1 - 1 / x) := by
    have hstep1 : (27 / 50 : ℝ) * (1 - 1 / x) ≤ Real.eulerMascheroniConstant * (1 - 1 / x) :=
      mul_le_mul_of_nonneg_right hγ.le h1mx_nn
    have hstep2 : (27 / 100 : ℝ) * (63 / 64) ≤ (27 / 100 : ℝ) * (1 - 1 / x) :=
      mul_le_mul_of_nonneg_left h1mx_ge (by norm_num only)
    linarith
  have hratio_full : (Real.log x + 1) / x ≤ (12 * Real.log 2 + 1) / 64 := by
    rw [← hratio64]
    exact hratio_le.trans hratio_anti
  unfold Analysis.primitiveReciprocalEvenMainError
  nlinarith [hterm1, hratio_full]

end PseudoPrime.LLS.Extensions
