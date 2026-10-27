/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapFullEndpointEven
public import PseudoPrime.LLS.FullEndpointPolynomial
public import PseudoPrime.Analysis.RealLog
public import PseudoPrime.Analysis.ExplicitLogSqrtAbsorption
public import PseudoPrime.LLS.ReciprocalGapEvenGamma
public import PseudoPrime.LLS.GammaSignedPrefixCharacterBounds
public import PseudoPrime.LLS.MidscaleEndpointRadius
public import PseudoPrime.Analysis.RetainedEvenReciprocalError
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.EvenLogWeightedUpper
public import PseudoPrime.LLS.FullEndpointEightNinthsRange
public import PseudoPrime.LLS.FullEndpointEightyOneRange
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Polynomial criterion for the parity-refined full endpoint -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Endpoint polynomial for the sharper reciprocal mass cap of an even primitive
character. It adds the exact mass-cap improvement to the general full-endpoint
polynomial, leaving the cutoff and all other analytic inputs unchanged. -/
noncomputable def fullEndpointEvenPolynomial (L P y z : ℝ) : ℝ :=
  fullEndpointPolynomial L P y z + (129 / 100 : ℝ) * y ^ 2 * (y + z + 1)

/-- Comparison polynomial after adding the even exact-log correction at the
uniform endpoint shift `73/50`. Its extra terms are the residual correction
and a nonnegative quadratic allowance. -/
noncomputable def fullEndpointEvenStarShiftPolynomial (L P y z : ℝ) : ℝ :=
  fullEndpointEvenPolynomial (L + 73 / 50) P y z +
    (y + z + 1) * (171 / 1000 * y ^ 2 - 4 * z - 103 / 40) +
    (y - 1) ^ 2 * (2 * z ^ 2 + z / 5 + 4)

/-- Direct scalar gap obtained by bounding the even reciprocal error at `y^2`
and inserting that bound into the exact logarithmic upper estimate. The first
term is the Riemann lower expression after the certified logarithmic main-error
bound is subtracted; the second term is the reciprocal contribution to the
exact logarithmic upper bound. -/
noncomputable def fullEndpointEvenExactComparisonGap (L P y z : ℝ) : ℝ :=
  y ^ 2 *
    ((1 - 1 / y) ^ 2 *
        (y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 -
          ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)) -
      (2 * y + 2 + 2 * z) *
        ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (2 * z - 31551 / 20000)))

/-- Denominator of the two-step endpoint correction. For `y ≥ 8` it is
positive, so division by it preserves the sign of the direct comparison gap. -/
noncomputable def fullEndpointEvenGapDenominator (y : ℝ) : ℝ :=
  (y - 1) * ((y + 1) ^ 2 + 2 * y * Real.log y)

/-- Polynomial numerator of the diagonal direct gap after collecting powers of
the radius and its logarithm. -/
noncomputable def fullEndpointEvenGapCorrectionNumerator (y : ℝ) : ℝ :=
  36620000 * y ^ 3 * Real.log y - 56749471 * y ^ 3 + 109860000 * y ^ 2 * (Real.log y) ^ 2 +
          73100099 * y ^ 2 * Real.log y +
          10777809 * y ^ 2 -
        73240000 * y * (Real.log y) ^ 2 -
        1528140 * y * Real.log y +
      2824690 * y -
    36620000 * (Real.log y) ^ 2 -
    177204180 * Real.log y -
    94877470

/-- Function form of the collected diagonal-gap numerator. Expressing sums,
products, and powers at the function level lets the derivative calculation use
the explicit sum and product rules below. -/
noncomputable def fullEndpointEvenGapCorrectionNumeratorFunction : ℝ → ℝ :=
  (fun x : ℝ => 36620000 * x ^ 3) * (fun x => Real.log x) - (fun x => 56749471 * x ^ 3) +
          (fun x => 109860000 * x ^ 2) * (fun x => (Real.log x) ^ 2) +
          (fun x => 73100099 * x ^ 2) * (fun x => Real.log x) +
          (fun x => 10777809 * x ^ 2) -
        (fun x => 73240000 * x) * (fun x => (Real.log x) ^ 2) -
        (fun x => 1528140 * x) * (fun x => Real.log x) +
      (fun x => 2824690 * x) -
    (fun x => 36620000 * (Real.log x) ^ 2) -
    (fun x => 177204180 * Real.log x) -
    (fun _ => (94877470 : ℝ))

/-- Derivative of the diagonal-gap numerator, collected by powers of the
radius and its logarithm. The proof expands the function-level operations and
then normalizes the resulting rational expression. -/
theorem deriv_fullEndpointEvenGapCorrectionNumerator {y : ℝ} (hy : 8 ≤ y) :
    deriv (fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) y =
      y ^ 2 * (109860000 * Real.log y - 133628413) +
              y * (219720000 * (Real.log y) ^ 2 + 365920198 * Real.log y + 94655717) -
            73240000 * (Real.log y) ^ 2 -
            148008140 * Real.log y +
          1296550 -
        (73240000 * Real.log y + 177204180) / y := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hpow3 : deriv (fun x : ℝ => x ^ 3) y = 3 * y ^ 2 := by
    change deriv ((fun x : ℝ => x) ^ 3) y = _
    rw [deriv_pow (by fun_prop) 3]
    simp only [deriv_id'']
    norm_num only [Nat.reduceSub, pow_one, mul_one]
  have hpow2 : deriv (fun x : ℝ => x ^ 2) y = 2 * y := by
    change deriv ((fun x : ℝ => x) ^ 2) y = _
    rw [deriv_pow (by fun_prop) 2]
    simp only [deriv_id'']
    norm_num only [Nat.reduceSub, pow_one, mul_one]
  have hlog2 : deriv (fun x : ℝ => (Real.log x) ^ 2) y = 2 * Real.log y / y := by
    change deriv ((fun x : ℝ => Real.log x) ^ 2) y = _
    rw [deriv_pow (Real.differentiableAt_log hyne) 2, Real.deriv_log]
    norm_num only [Nat.reduceSub, pow_one, mul_one]
    field_simp [hyne]
  have hfunction :
    (fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) =
      fullEndpointEvenGapCorrectionNumeratorFunction := by
    funext x
    rfl
  rw [hfunction]
  unfold fullEndpointEvenGapCorrectionNumeratorFunction
  simp (discharger := fun_prop (disch := exact hyne)) only [deriv_add, deriv_sub, deriv_const_mul,
    deriv_mul, Real.deriv_log]
  rw [hpow3, hpow2, hlog2]
  simp only [deriv_const_mul_id, deriv_const]
  field_simp [hyne]
  ring_nf

/-- Normalized endpoint gap at the diagonal level `L = y`. This correction
measures how far the direct gap permits lowering the logarithmic cutoff. -/
noncomputable def fullEndpointEvenGapCorrection (y : ℝ) : ℝ :=
  fullEndpointEvenGapCorrectionNumerator y / (18310000 * fullEndpointEvenGapDenominator y)

/-- First fixed substitution in the endpoint correction. The maximum keeps the
radius in the certified domain beginning at eight. -/
noncomputable def fullEndpointEvenCorrectionFirstRadius (L : ℝ) : ℝ :=
  max 8 (L - fullEndpointEvenGapCorrection L)

/-- Second fixed substitution in the endpoint correction. -/
noncomputable def fullEndpointEvenCorrectionSecondRadius (L : ℝ) : ℝ :=
  L - fullEndpointEvenGapCorrection (fullEndpointEvenCorrectionFirstRadius L)

/-- Two-substitution endpoint witness cutoff, equal to the square of the
second corrected radius. -/
noncomputable def fullEndpointEvenTwoStepCutoff (L : ℝ) : ℝ :=
  fullEndpointEvenCorrectionSecondRadius L ^ 2

/-- The quadratic coefficient in the derivative numerator of the normalized
endpoint correction. -/
noncomputable def fullEndpointEvenCorrectionQ2 (y : ℝ) : ℝ :=
  12 * y ^ 4 - (119089 / 5000 : ℝ) * y ^ 3 + (4339 / 125 : ℝ) * y ^ 2 - (3339 / 250 : ℝ) * y

/-- The linear coefficient in the derivative numerator of the normalized
endpoint correction. -/
noncomputable def fullEndpointEvenCorrectionQ1 (y : ℝ) : ℝ :=
  (38089 / 10000 : ℝ) * y ^ 5 + (21411 / 2500 : ℝ) * y ^ 4 + (16393 / 10000 : ℝ) * y ^ 3 +
        (100491 / 5000 : ℝ) * y ^ 2 -
      (3979 / 500 : ℝ) * y +
    4

/-- The constant coefficient in the derivative numerator of the normalized
endpoint correction. -/
noncomputable def fullEndpointEvenCorrectionQ0 (y : ℝ) : ℝ :=
  (85031 / 10000 : ℝ) * y ^ 5 + (4231 / 10000 : ℝ) * y ^ 4 + (92153 / 10000 : ℝ) * y ^ 3 +
        (62713 / 10000 : ℝ) * y ^ 2 -
      (2969 / 500 : ℝ) * y +
    4839 / 500

/-- Numerator in the derivative formula for the normalized endpoint correction,
with the logarithmic variable kept explicit. -/
noncomputable def fullEndpointEvenCorrectionDerivativeNumerator (y z : ℝ) : ℝ :=
  (2 * y ^ 5 + 4 * y * (y - 1) ^ 2 * z) * (y - z ^ 2) + fullEndpointEvenCorrectionQ2 y * z ^ 2 +
    fullEndpointEvenCorrectionQ1 y * z +
    fullEndpointEvenCorrectionQ0 y

/-- The three derivative coefficient polynomials are positive for all radii
from two onward. -/
theorem fullEndpointEvenCorrectionQ2_pos {y : ℝ} (hy : 2 ≤ y) :
    0 < fullEndpointEvenCorrectionQ2 y := by
  have hypos : 0 < y := by linarith only [hy]
  have hA : 0 < 12 * y - (119089 / 5000 : ℝ) := by nlinarith only [hy]
  have hB : 0 < (4339 / 125 : ℝ) * y - 3339 / 250 := by nlinarith only [hy]
  have hfactor :
    fullEndpointEvenCorrectionQ2 y =
      y * (y ^ 2 * (12 * y - 119089 / 5000) + (4339 / 125 * y - 3339 / 250)) := by
    unfold fullEndpointEvenCorrectionQ2
    ring
  rw [hfactor]
  exact mul_pos hypos (add_pos (mul_pos (sq_pos_of_pos hypos) hA) hB)

/-- The second derivative coefficient polynomial is positive from radius two. -/
theorem fullEndpointEvenCorrectionQ1_pos {y : ℝ} (hy : 2 ≤ y) :
    0 < fullEndpointEvenCorrectionQ1 y := by
  have hypos : 0 < y := by linarith only [hy]
  have hySq : 4 ≤ y ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hy (le_of_lt hypos)
    nlinarith only [hy, hmul]
  have hyFourth : 16 ≤ y ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hySq (sq_nonneg y)
    nlinarith only [hySq, hmul]
  have hdominant : 0 < (38089 / 10000 : ℝ) * y ^ 4 - 3979 / 500 := by nlinarith only [hyFourth]
  have hterm3 : 0 < (21411 / 2500 : ℝ) * y ^ 3 := mul_pos (by norm_num only) (pow_pos hypos 3)
  have hterm2 : 0 < (16393 / 10000 : ℝ) * y ^ 2 := mul_pos (by norm_num only) (pow_pos hypos 2)
  have hterm1 : 0 < (100491 / 5000 : ℝ) * y := mul_pos (by norm_num only) hypos
  have hinner :
    0 <
      (38089 / 10000 : ℝ) * y ^ 4 - 3979 / 500 + (21411 / 2500 : ℝ) * y ^ 3 +
        (16393 / 10000 : ℝ) * y ^ 2 +
        (100491 / 5000 : ℝ) * y := by
    exact add_pos (add_pos (add_pos hdominant hterm3) hterm2) hterm1
  have hfactor :
    fullEndpointEvenCorrectionQ1 y =
      y *
          ((38089 / 10000 : ℝ) * y ^ 4 - 3979 / 500 + (21411 / 2500 : ℝ) * y ^ 3 +
            (16393 / 10000 : ℝ) * y ^ 2 +
            (100491 / 5000 : ℝ) * y) +
        4 := by
    unfold fullEndpointEvenCorrectionQ1
    ring
  rw [hfactor]
  exact add_pos (mul_pos hypos hinner) (by norm_num only)

/-- The constant derivative coefficient polynomial is positive from radius two. -/
theorem fullEndpointEvenCorrectionQ0_pos {y : ℝ} (hy : 2 ≤ y) :
    0 < fullEndpointEvenCorrectionQ0 y := by
  have hypos : 0 < y := by linarith only [hy]
  have hySq : 4 ≤ y ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hy (le_of_lt hypos)
    nlinarith only [hy, hmul]
  have hyFourth : 16 ≤ y ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hySq (sq_nonneg y)
    nlinarith only [hySq, hmul]
  have hdominant : 0 < (85031 / 10000 : ℝ) * y ^ 4 - 2969 / 500 := by nlinarith only [hyFourth]
  have hterm3 : 0 < (4231 / 10000 : ℝ) * y ^ 3 := mul_pos (by norm_num only) (pow_pos hypos 3)
  have hterm2 : 0 < (92153 / 10000 : ℝ) * y ^ 2 := mul_pos (by norm_num only) (pow_pos hypos 2)
  have hterm1 : 0 < (62713 / 10000 : ℝ) * y :=
    mul_pos (by norm_num only) (by nlinarith only [hypos])
  have hinner :
    0 <
      (85031 / 10000 : ℝ) * y ^ 4 - 2969 / 500 + (4231 / 10000 : ℝ) * y ^ 3 +
        (92153 / 10000 : ℝ) * y ^ 2 +
        (62713 / 10000 : ℝ) * y := by
    exact add_pos (add_pos (add_pos hdominant hterm3) hterm2) hterm1
  have hfactor :
    fullEndpointEvenCorrectionQ0 y =
      y *
          ((85031 / 10000 : ℝ) * y ^ 4 - 2969 / 500 + (4231 / 10000 : ℝ) * y ^ 3 +
            (92153 / 10000 : ℝ) * y ^ 2 +
            (62713 / 10000 : ℝ) * y) +
        4839 / 500 := by
    unfold fullEndpointEvenCorrectionQ0
    ring
  rw [hfactor]
  exact add_pos (mul_pos hypos hinner) (by norm_num only)

/-- The derivative numerator is strictly positive for the actual logarithmic
variable on radii from eight onward, using `log y ≥ 0` and `(log y)^2 ≤ y`. -/
theorem fullEndpointEvenCorrectionDerivativeNumerator_pos {y : ℝ} (hy : 8 ≤ y) (hz : 0 ≤ Real.log y)
    (hzsq : (Real.log y) ^ 2 ≤ y) :
    0 < fullEndpointEvenCorrectionDerivativeNumerator y (Real.log y) := by
  have hypos : 0 < y := by linarith only [hy]
  have hcoefA : 0 ≤ 2 * y ^ 5 := le_of_lt (mul_pos (by norm_num only) (pow_pos hypos 5))
  have hcoefB : 0 ≤ 4 * y * (y - 1) ^ 2 * Real.log y :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hypos.le) (sq_nonneg (y - 1))) hz
  have hcoef : 0 ≤ 2 * y ^ 5 + 4 * y * (y - 1) ^ 2 * Real.log y := add_nonneg hcoefA hcoefB
  have hmain : 0 ≤ (2 * y ^ 5 + 4 * y * (y - 1) ^ 2 * Real.log y) * (y - (Real.log y) ^ 2) :=
    mul_nonneg hcoef (sub_nonneg.mpr hzsq)
  have hq2 : 0 ≤ fullEndpointEvenCorrectionQ2 y * (Real.log y) ^ 2 :=
    mul_nonneg (fullEndpointEvenCorrectionQ2_pos (y := y) (by linarith only [hy])).le
      (sq_nonneg (Real.log y))
  have hq1 : 0 ≤ fullEndpointEvenCorrectionQ1 y * Real.log y :=
    mul_nonneg (fullEndpointEvenCorrectionQ1_pos (y := y) (by linarith only [hy])).le hz
  have hq0 : 0 < fullEndpointEvenCorrectionQ0 y :=
    fullEndpointEvenCorrectionQ0_pos (y := y) (by linarith only [hy])
  exact add_pos_of_nonneg_of_pos (add_nonneg (add_nonneg hmain hq2) hq1) hq0

/-- The squared logarithm is bounded by the radius from eight onward. -/
theorem log_sq_le_self_of_eight_le {y : ℝ} (hy : 8 ≤ y) : (Real.log y) ^ 2 ≤ y := by
  have hypos : 0 < y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hlog := Analysis.log_le_sqrt_of_pos hypos
  have hsquare := Real.sq_sqrt hypos.le
  nlinarith only [hz, hlog, Real.sqrt_nonneg y, hsquare]

/-- The diagonal exact comparison gap is differentiable at every radius from
eight onward. -/
theorem fullEndpointEvenDiagonalGap_differentiableAt {y : ℝ} (hy : 8 ≤ y) :
    DifferentiableAt ℝ
      (fun x : ℝ => fullEndpointEvenExactComparisonGap x (2096 / 1831) x (Real.log x)) y := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hy2ne : y ^ 2 ≠ 0 := pow_ne_zero 2 hyne
  unfold fullEndpointEvenExactComparisonGap
  fun_prop (disch :=
    first
    | exact hyne
    | exact hy2ne)

/-- The endpoint correction denominator is differentiable at every radius from
eight onward. -/
theorem fullEndpointEvenGapDenominator_differentiableAt {y : ℝ} (hy : 8 ≤ y) :
    DifferentiableAt ℝ (fun x : ℝ => fullEndpointEvenGapDenominator x) y := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  unfold fullEndpointEvenGapDenominator
  fun_prop (disch := exact hyne)

/-- The diagonal direct gap is the collected numerator divided by the exact
scale factor. This normal form simplifies the subsequent derivative identity. -/
theorem fullEndpointEvenExactComparisonGap_diagonal_eq_correctionNumerator {y : ℝ} (hy : 8 ≤ y) :
    fullEndpointEvenExactComparisonGap y (2096 / 1831) y (Real.log y) =
      fullEndpointEvenGapCorrectionNumerator y / 18310000 := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  unfold fullEndpointEvenExactComparisonGap fullEndpointEvenGapCorrectionNumerator
  field_simp [hyne]
  ring_nf

/-- The denominator derivative has the displayed elementary logarithmic form.
This is the denominator-side computation used to normalize the derivative of
the endpoint correction. -/
theorem deriv_fullEndpointEvenGapDenominator {y : ℝ} (hy : 8 ≤ y) :
    deriv (fun x : ℝ => fullEndpointEvenGapDenominator x) y =
      3 * y ^ 2 + 4 * y - 3 + (4 * y - 2) * Real.log y := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hA : DifferentiableAt ℝ (fun x : ℝ => x - 1) y := by fun_prop
  have hB : DifferentiableAt ℝ (fun x : ℝ => (x + 1) ^ 2 + 2 * x * Real.log x) y := by
    fun_prop (disch := exact hyne)
  unfold fullEndpointEvenGapDenominator
  change deriv ((fun x : ℝ => x - 1) * (fun x => (x + 1) ^ 2 + 2 * x * Real.log x)) y = _
  rw [deriv_mul hA hB]
  have hA' : deriv (fun x : ℝ => x - 1) y = 1 := by simp only [deriv_sub_const, deriv_id'']
  have hB1' : deriv (fun x : ℝ => (x + 1) ^ 2) y = 2 * (y + 1) := by
    change deriv ((fun x : ℝ => x + 1) ^ 2) y = _
    rw [deriv_pow (by fun_prop) 2]
    simp only [deriv_add_const, deriv_id'']
    norm_num only [Nat.reduceSub, pow_one, mul_one]
  have hB2' : deriv (fun x : ℝ => 2 * x * Real.log x) y = 2 * Real.log y + 2 := by
    change deriv ((fun x : ℝ => 2 * x) * (fun x => Real.log x)) y = _
    rw [deriv_mul (by fun_prop) (Real.differentiableAt_log hyne)]
    simp only [deriv_const_mul_id]
    rw [Real.deriv_log]
    field_simp [hyne]
  have hB' :
    deriv (fun x : ℝ => (x + 1) ^ 2 + 2 * x * Real.log x) y = 2 * (y + 1) + 2 * Real.log y + 2 := by
    change deriv ((fun x : ℝ => (x + 1) ^ 2) + (fun x => 2 * x * Real.log x)) y = _
    rw [deriv_add (by fun_prop) (by fun_prop (disch := exact hyne)), hB1', hB2']
    ring_nf
  rw [hA', hB']
  ring_nf

/-- The denominator of the normalized endpoint correction is positive from
radius eight onward. -/
theorem fullEndpointEvenGapDenominator_pos {y : ℝ} (hy : 8 ≤ y) :
    0 < fullEndpointEvenGapDenominator y := by
  have hypos : 0 < y := by linarith only [hy]
  have hylog : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hfirst : 0 < y - 1 := by linarith only [hy]
  have hsecond : 0 < (y + 1) ^ 2 + 2 * y * Real.log y := by
    have hsquare : 0 < (y + 1) ^ 2 := sq_pos_of_pos (by linarith only [hy])
    have hproduct : 0 ≤ 2 * y * Real.log y :=
      mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (le_of_lt hypos)) hylog
    exact add_pos_of_pos_of_nonneg hsquare hproduct
  exact mul_pos hfirst hsecond

/-- Derivative of the normalized endpoint correction. Its numerator is the
positive expression already bounded in `fullEndpointEvenCorrectionDerivativeNumerator_pos`. -/
theorem deriv_fullEndpointEvenGapCorrection {y : ℝ} (hy : 8 ≤ y) :
    deriv (fun x : ℝ => fullEndpointEvenGapCorrection x) y =
      fullEndpointEvenCorrectionDerivativeNumerator y (Real.log y) /
        (y * (fullEndpointEvenGapDenominator y) ^ 2) := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hfunction :
    (fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) =
      fullEndpointEvenGapCorrectionNumeratorFunction := by
    funext x
    rfl
  have hM : DifferentiableAt ℝ (fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) y := by
    rw [hfunction]
    unfold fullEndpointEvenGapCorrectionNumeratorFunction
    fun_prop (disch := exact hyne)
  have hMFunction : DifferentiableAt ℝ fullEndpointEvenGapCorrectionNumeratorFunction y := by
    rw [← hfunction]
    exact hM
  have hD := fullEndpointEvenGapDenominator_differentiableAt hy
  have hscaledD := hD.const_mul (18310000 : ℝ)
  have hDne : fullEndpointEvenGapDenominator y ≠ 0 :=
    ne_of_gt (fullEndpointEvenGapDenominator_pos hy)
  have hden : 18310000 * fullEndpointEvenGapDenominator y ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num only) (fullEndpointEvenGapDenominator_pos hy))
  unfold fullEndpointEvenGapCorrection
  change
    deriv
        ((fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) /
          (fun x => 18310000 * fullEndpointEvenGapDenominator x))
        y =
      _
  rw [hfunction, deriv_div hMFunction hscaledD hden, deriv_const_mul 18310000 hD, ← hfunction]
  rw [deriv_fullEndpointEvenGapCorrectionNumerator hy, deriv_fullEndpointEvenGapDenominator hy]
  unfold fullEndpointEvenGapDenominator at hDne ⊢
  unfold fullEndpointEvenGapCorrectionNumerator fullEndpointEvenCorrectionDerivativeNumerator
    fullEndpointEvenCorrectionQ2 fullEndpointEvenCorrectionQ1 fullEndpointEvenCorrectionQ0
  field_simp [hyne, hDne]
  ring_nf

/-- The normalized endpoint correction is differentiable at every radius at
least eight. The numerator is differentiable by its function-level form, and
the positive denominator permits the quotient rule. -/
theorem fullEndpointEvenGapCorrection_differentiableAt {y : ℝ} (hy : 8 ≤ y) :
    DifferentiableAt ℝ (fun x : ℝ => fullEndpointEvenGapCorrection x) y := by
  have hyne : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hfunction :
    (fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) =
      fullEndpointEvenGapCorrectionNumeratorFunction := by
    funext x
    rfl
  have hM : DifferentiableAt ℝ (fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) y := by
    rw [hfunction]
    unfold fullEndpointEvenGapCorrectionNumeratorFunction
    fun_prop (disch := exact hyne)
  have hD := fullEndpointEvenGapDenominator_differentiableAt hy
  have hscaledD := hD.const_mul (18310000 : ℝ)
  have hden : 18310000 * fullEndpointEvenGapDenominator y ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num only) (fullEndpointEvenGapDenominator_pos hy))
  unfold fullEndpointEvenGapCorrection
  change
    DifferentiableAt ℝ
      ((fun x : ℝ => fullEndpointEvenGapCorrectionNumerator x) /
        (fun x => 18310000 * fullEndpointEvenGapDenominator x))
      y
  rw [hfunction]
  exact hM.div hscaledD hden

/-- The endpoint correction has positive derivative from radius eight onward.
The derivative numerator and its denominator are both positive on this range. -/
theorem fullEndpointEvenGapCorrection_deriv_pos {y : ℝ} (hy : 8 ≤ y) :
    0 < deriv (fun x : ℝ => fullEndpointEvenGapCorrection x) y := by
  rw [deriv_fullEndpointEvenGapCorrection hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hn := fullEndpointEvenCorrectionDerivativeNumerator_pos hy hz (log_sq_le_self_of_eight_le hy)
  have hypos : 0 < y := by linarith only [hy]
  have hDpos := fullEndpointEvenGapDenominator_pos hy
  have hden : 0 < y * fullEndpointEvenGapDenominator y ^ 2 := mul_pos hypos (sq_pos_of_pos hDpos)
  exact div_pos hn hden

/-- The endpoint correction is strictly increasing on radii from eight
onward, as its derivative is positive throughout that interval. -/
theorem fullEndpointEvenGapCorrection_strictMonoOn :
    StrictMonoOn fullEndpointEvenGapCorrection (Set.Ici (8 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (8 : ℝ))
  · intro x hx
    exact (fullEndpointEvenGapCorrection_differentiableAt hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact fullEndpointEvenGapCorrection_deriv_pos (le_of_lt hx)

/-- The direct gap is affine in the logarithmic level with slope equal to the
negative denominator. Consequently the normalized diagonal gap gives an exact
cutoff correction at every level. -/
theorem fullEndpointEvenExactComparisonGap_eq_denominator_correction {L y : ℝ} (hy : 8 ≤ y) :
    fullEndpointEvenExactComparisonGap L (2096 / 1831) y (Real.log y) =
      fullEndpointEvenGapDenominator y * (y + fullEndpointEvenGapCorrection y - L) := by
  have hy0 : y ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hy)
  have hD : fullEndpointEvenGapDenominator y ≠ 0 := ne_of_gt (fullEndpointEvenGapDenominator_pos hy)
  have hdiff :
    fullEndpointEvenExactComparisonGap L (2096 / 1831) y (Real.log y) -
        fullEndpointEvenExactComparisonGap y (2096 / 1831) y (Real.log y) =
      fullEndpointEvenGapDenominator y * (y - L) := by
    unfold fullEndpointEvenGapDenominator fullEndpointEvenExactComparisonGap
    field_simp [hy0]
    ring
  have hmul :
    fullEndpointEvenGapDenominator y * fullEndpointEvenGapCorrection y =
      fullEndpointEvenExactComparisonGap y (2096 / 1831) y (Real.log y) := by
    unfold fullEndpointEvenGapCorrection
    rw [fullEndpointEvenExactComparisonGap_diagonal_eq_correctionNumerator hy]
    field_simp [hD]
  linear_combination hdiff - hmul

/-- The shifted even endpoint polynomial is bounded by the direct exact-log
comparison gap. Their difference is `(y-1)^2 z (P-9/8)` plus a positive
rational term, so the certified lower bound for `log pi` closes the comparison. -/
theorem fullEndpointEvenStarShiftPolynomial_le_exact_comparison_gap {L P y z : ℝ} (hy : y ≠ 0)
    (hz : 0 ≤ z) (hP : 9 / 8 ≤ P) :
    fullEndpointEvenStarShiftPolynomial (L - 73 / 50) P y z ≤
      fullEndpointEvenExactComparisonGap L P y z := by
  have hd :
    fullEndpointEvenExactComparisonGap L P y z -
        fullEndpointEvenStarShiftPolynomial (L - 73 / 50) P y z =
      (y - 1) ^ 2 * (P * z - (9 / 8 : ℝ) * z + 88 / 1000) := by
    unfold fullEndpointEvenExactComparisonGap fullEndpointEvenStarShiftPolynomial
      fullEndpointEvenPolynomial fullEndpointPolynomial
    field_simp [hy]
    ring
  have hc : 0 ≤ P * z - (9 / 8 : ℝ) * z + 88 / 1000 := by nlinarith only [hz, hP]
  have hn := mul_nonneg (sq_nonneg (y - 1)) hc
  linarith only [hd, hn]

/-- Scalar form of the direct endpoint comparison. If the reciprocal character
sum has the exact even upper bound, and the logarithmic sum has its character
upper bound and Riemann lower bound, then the comparison gap is nonpositive. -/
theorem fullEndpointEvenExactComparisonGap_nonpos {L P y z B S : ℝ} (hy : 8 ≤ y) (hz : 0 ≤ z)
    (hrec :
      2 * z - 31551 / 20000 ≤
        (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (1 - 1 / y) ^ 2 * B)
    (hupper : S ≤ (2 * y + 2 + 2 * z) * B + (L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)
    (hlower : y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 ≤ S) :
    fullEndpointEvenExactComparisonGap L P y z ≤ 0 := by
  have hk : 0 ≤ (1 - 1 / y) ^ 2 := sq_nonneg (1 - 1 / y)
  have hC : 0 ≤ 2 * y + 2 + 2 * z := by nlinarith only [hy, hz]
  have hB :
    (1 - 1 / y) ^ 2 * B ≤
      (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
        (2 * z - 31551 / 20000) := by
    linarith only [hrec]
  have hV :
    y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 -
        ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2) ≤
      (2 * y + 2 + 2 * z) * B := by
    linarith only [hlower, hupper]
  have hVk := mul_le_mul_of_nonneg_left hV hk
  have hBk := mul_le_mul_of_nonneg_right hB hC
  have hscalar :
    (1 - 1 / y) ^ 2 *
        (y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 -
          ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)) ≤
      (2 * y + 2 + 2 * z) *
        ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
          (2 * z - 31551 / 20000)) := by
    nlinarith only [hVk, hBk]
  have hid :
    fullEndpointEvenExactComparisonGap L P y z =
      y ^ 2 *
        ((1 - 1 / y) ^ 2 *
            (y ^ 2 - y / 20 - (1839 / 500 : ℝ) * z - 21 / 20 -
              ((L - P) * z + 103 / 250 - (23 / 40) * z - 2 * z ^ 2)) -
          (2 * y + 2 + 2 * z) *
            ((1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (L - P) - 1961 / 2000 + (2 * z + 103 / 80) / y ^ 2 -
              (2 * z - 31551 / 20000))) := by
    rfl
  rw [hid]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (by linarith only [hscalar])

/-- The direct endpoint gap is monotone in the pi-log parameter. Its exact
coefficient is `(y - 1) * ((y + 1)^2 + 2*y*z)`. -/
theorem fullEndpointEvenExactComparisonGap_mono_pi {L P Q y z : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z)
    (hPQ : P ≤ Q) :
    fullEndpointEvenExactComparisonGap L P y z ≤ fullEndpointEvenExactComparisonGap L Q y z := by
  have hdiff :
    fullEndpointEvenExactComparisonGap L Q y z - fullEndpointEvenExactComparisonGap L P y z =
      (Q - P) * (y - 1) * ((y + 1) ^ 2 + 2 * y * z) := by
    unfold fullEndpointEvenExactComparisonGap
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hy)]
    ring
  have hzfactor : 0 ≤ (y + 1) ^ 2 + 2 * y * z := by positivity
  have hnonneg : 0 ≤ (Q - P) * (y - 1) * ((y + 1) ^ 2 + 2 * y * z) := by
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hPQ) (sub_nonneg.mpr hy)) hzfactor
  have hdiffNonneg :
    0 ≤
      fullEndpointEvenExactComparisonGap L Q y z - fullEndpointEvenExactComparisonGap L P y z := by
    rw [hdiff]
    exact hnonneg
  linarith only [hdiffNonneg]

/-- The direct endpoint gap is antitone in the conductor-log parameter. -/
theorem fullEndpointEvenExactComparisonGap_antitone_level {L K P y z : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z)
    (hLK : L ≤ K) :
    fullEndpointEvenExactComparisonGap K P y z ≤ fullEndpointEvenExactComparisonGap L P y z := by
  have hdiff :
    fullEndpointEvenExactComparisonGap K P y z - fullEndpointEvenExactComparisonGap L P y z =
      -(K - L) * (y - 1) * ((y + 1) ^ 2 + 2 * y * z) := by
    unfold fullEndpointEvenExactComparisonGap
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hy)]
    ring
  have hfactor : 0 ≤ (y + 1) ^ 2 + 2 * y * z := by positivity
  have hnonneg : 0 ≤ (K - L) * (y - 1) * ((y + 1) ^ 2 + 2 * y * z) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hLK) (sub_nonneg.mpr hy)) hfactor
  have hdiffNonpos :
    fullEndpointEvenExactComparisonGap K P y z - fullEndpointEvenExactComparisonGap L P y z ≤
      0 := by
    rw [hdiff]
    nlinarith only [hnonneg]
  linarith only [hdiffNonpos]

/-- At radius eight, the exact comparison gap is increasing in its log-radius
argument from the certified lower bound `2079/1000`. -/
theorem fullEndpointEvenExactComparisonGap_eight_mono_log {z : ℝ} (hz : 2079 / 1000 ≤ z) :
    fullEndpointEvenExactComparisonGap (56 / 5) (2096 / 1831) 8 (2079 / 1000) ≤
      fullEndpointEvenExactComparisonGap (56 / 5) (2096 / 1831) 8 z := by
  have hdiff :
    fullEndpointEvenExactComparisonGap (56 / 5) (2096 / 1831) 8 z -
        fullEndpointEvenExactComparisonGap (56 / 5) (2096 / 1831) 8 (2079 / 1000) =
      (z - 2079 / 1000) * (350 * (z + 2079 / 1000) + 4169028259 / 4577500) := by
    unfold fullEndpointEvenExactComparisonGap
    field_simp
    ring
  have hfactor : 0 ≤ 350 * (z + 2079 / 1000) + 4169028259 / 4577500 := by positivity
  have hdiffNonneg :
    0 ≤
      fullEndpointEvenExactComparisonGap (56 / 5) (2096 / 1831) 8 z -
        fullEndpointEvenExactComparisonGap (56 / 5) (2096 / 1831) 8 (2079 / 1000) := by
    rw [hdiff]
    exact mul_nonneg (sub_nonneg.mpr hz) hfactor
  linarith only [hdiffNonneg]

/-- At radius twenty-four, the exact comparison gap is increasing in its
log-radius argument from `1589/500`. -/
theorem fullEndpointEvenExactComparisonGap_twentyFour_mono_log {z : ℝ} (hz : 1589 / 500 ≤ z) :
    fullEndpointEvenExactComparisonGap (144 / 5) (2096 / 1831) 24 (1589 / 500) ≤
      fullEndpointEvenExactComparisonGap (144 / 5) (2096 / 1831) 24 z := by
  have hdiff :
    fullEndpointEvenExactComparisonGap (144 / 5) (2096 / 1831) 24 z -
        fullEndpointEvenExactComparisonGap (144 / 5) (2096 / 1831) 24 (1589 / 500) =
      (z - 1589 / 500) * (3358 * (z + 1589 / 500) + 112774576371 / 4577500) := by
    unfold fullEndpointEvenExactComparisonGap
    field_simp
    ring
  have hfactor : 0 ≤ 3358 * (z + 1589 / 500) + 112774576371 / 4577500 := by positivity
  have hdiffNonneg :
    0 ≤
      fullEndpointEvenExactComparisonGap (144 / 5) (2096 / 1831) 24 z -
        fullEndpointEvenExactComparisonGap (144 / 5) (2096 / 1831) 24 (1589 / 500) := by
    rw [hdiff]
    exact mul_nonneg (sub_nonneg.mpr hz) hfactor
  linarith only [hdiffNonneg]

/-- The direct gap at radius eight is positive when the conductor logarithm is
at most `56/5`. Use the certified rational lower bound for `log 8` and level
antitonicity to cover the entire lower range. -/
theorem fullEndpointEvenExactComparisonGap_pos_at_eight {L : ℝ} (hL : L ≤ 56 / 5) :
    0 < fullEndpointEvenExactComparisonGap L (2096 / 1831) 8 (Real.log 8) := by
  have hlog : (2079 / 1000 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hanchor : 0 < fullEndpointEvenExactComparisonGap (56 / 5) (2096 / 1831) 8 (2079 / 1000) := by
    norm_num only [fullEndpointEvenExactComparisonGap]
  have hz := fullEndpointEvenExactComparisonGap_eight_mono_log hlog
  have hlevel :=
    fullEndpointEvenExactComparisonGap_antitone_level (L := L) (K := (56 / 5 : ℝ)) (P :=
      (2096 / 1831 : ℝ)) (y := (8 : ℝ)) (z := Real.log 8) (by norm_num only)
      (Real.log_nonneg (by norm_num only)) hL
  linarith only [hanchor, hz, hlevel]

/-- The normalized endpoint correction at radius eight exceeds `16/5`.
The positive direct gap at level `56/5` gives this lower bound after dividing
by the positive endpoint denominator. This estimate supplies the lower side
of the two-sided anchor needed for monotonicity and the fixed substitutions. -/
theorem fullEndpointEvenGapCorrection_eight_gt :
    (16 / 5 : ℝ) < fullEndpointEvenGapCorrection 8 := by
  have hgap := fullEndpointEvenExactComparisonGap_pos_at_eight (L := (56 / 5 : ℝ)) le_rfl
  have hid :=
    fullEndpointEvenExactComparisonGap_eq_denominator_correction (L := (56 / 5 : ℝ)) (y := (8 : ℝ))
      (by norm_num only)
  rw [hid, show (56 / 5 : ℝ) = 8 + 16 / 5 by norm_num only] at hgap
  have hmul :
    0 < fullEndpointEvenGapDenominator 8 * (fullEndpointEvenGapCorrection 8 - 16 / 5) := by
    nlinarith only [hgap]
  have hD := fullEndpointEvenGapDenominator_pos (y := (8 : ℝ)) (by norm_num only)
  rcases mul_pos_iff.mp hmul with ⟨_, hcor⟩ | ⟨hDneg, _⟩
  · linarith only [hcor]
  · linarith only [hD, hDneg]

/-- The normalized endpoint correction at radius eight is below `7/2`.
The comparison gap at level `23/2` is negative at the rational log bound
`21/10`; its exact quadratic dependence on the log radius transfers that sign
to `Real.log 8`. -/
theorem fullEndpointEvenGapCorrection_eight_lt : fullEndpointEvenGapCorrection 8 < (7 / 2 : ℝ) := by
  have hloglo : (2079 / 1000 : ℝ) ≤ Real.log 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hloghi : Real.log 8 ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  have hdiff :
    fullEndpointEvenExactComparisonGap (23 / 2) (2096 / 1831) 8 (21 / 10) -
        fullEndpointEvenExactComparisonGap (23 / 2) (2096 / 1831) 8 (Real.log 8) =
      (21 / 10 - Real.log 8) * (350 * (21 / 10 + Real.log 8) + 4015224259 / 4577500) := by
    unfold fullEndpointEvenExactComparisonGap
    field_simp
    ring_nf
  have hfactor : 0 ≤ 350 * (21 / 10 + Real.log 8) + 4015224259 / 4577500 := by positivity
  have hgap_le :
    fullEndpointEvenExactComparisonGap (23 / 2) (2096 / 1831) 8 (Real.log 8) ≤
      fullEndpointEvenExactComparisonGap (23 / 2) (2096 / 1831) 8 (21 / 10) := by
    rw [← sub_nonneg]
    rw [hdiff]
    exact mul_nonneg (sub_nonneg.mpr hloghi) hfactor
  have hgap : fullEndpointEvenExactComparisonGap (23 / 2) (2096 / 1831) 8 (Real.log 8) < 0 := by
    have hup : fullEndpointEvenExactComparisonGap (23 / 2) (2096 / 1831) 8 (21 / 10) < 0 := by
      norm_num only [fullEndpointEvenExactComparisonGap]
    linarith only [hgap_le, hup]
  have hid :=
    fullEndpointEvenExactComparisonGap_eq_denominator_correction (L := (23 / 2 : ℝ)) (y := (8 : ℝ))
      (by norm_num only)
  rw [hid, show (23 / 2 : ℝ) = 8 + 7 / 2 by norm_num only] at hgap
  have hmul : fullEndpointEvenGapDenominator 8 * (fullEndpointEvenGapCorrection 8 - 7 / 2) < 0 := by
    nlinarith only [hgap]
  have hD := fullEndpointEvenGapDenominator_pos (y := (8 : ℝ)) (by norm_num only)
  rcases mul_neg_iff.mp hmul with ⟨_, hcor⟩ | ⟨hDneg, _⟩
  · linarith only [hcor]
  · linarith only [hD, hDneg]

/-- The first corrected radius stays below the ambient logarithmic level once
the latter reaches `23/2`. Positivity of the correction follows by comparing
it with its value at radius eight. -/
theorem fullEndpointEvenCorrectionFirstRadius_lt {L : ℝ} (hL : 23 / 2 ≤ L) :
    fullEndpointEvenCorrectionFirstRadius L < L := by
  have hL8 : (8 : ℝ) < L := by linarith only [hL]
  have h8mem : (8 : ℝ) ∈ Set.Ici 8 := by norm_num only [Set.mem_Ici]
  have hLmem : L ∈ Set.Ici 8 := le_of_lt hL8
  have hH8L : fullEndpointEvenGapCorrection 8 < fullEndpointEvenGapCorrection L :=
    fullEndpointEvenGapCorrection_strictMonoOn h8mem hLmem hL8
  have hHpos : 0 < fullEndpointEvenGapCorrection L :=
    lt_trans (by norm_num only : (0 : ℝ) < 16 / 5)
      (lt_trans fullEndpointEvenGapCorrection_eight_gt hH8L)
  unfold fullEndpointEvenCorrectionFirstRadius
  rw [max_lt_iff]
  constructor
  · exact hL8
  · linarith only [hHpos]

/-- The second corrected radius is strictly larger than the first. If the first
radius is eight, use the upper anchor for `H(8)`; otherwise strict monotonicity
compares `H` at the first radius and at the ambient level. -/
theorem fullEndpointEvenCorrectionSecondRadius_gt_first {L : ℝ} (hL : 23 / 2 ≤ L) :
    fullEndpointEvenCorrectionFirstRadius L < fullEndpointEvenCorrectionSecondRadius L := by
  let a := fullEndpointEvenCorrectionFirstRadius L
  have hL8 : (8 : ℝ) < L := by linarith only [hL]
  have ha8 : 8 ≤ a := by
    dsimp only [a, fullEndpointEvenCorrectionFirstRadius]
    exact le_max_left _ _
  have haL : a < L := by
    dsimp only [a]
    exact fullEndpointEvenCorrectionFirstRadius_lt hL
  by_cases hlarge : 8 ≤ L - fullEndpointEvenGapCorrection L
  · have haeq : a = L - fullEndpointEvenGapCorrection L := by
      dsimp only [a, fullEndpointEvenCorrectionFirstRadius]
      exact max_eq_right hlarge
    have hAmem : a ∈ Set.Ici (8 : ℝ) := ha8
    have hLmem : L ∈ Set.Ici (8 : ℝ) := le_of_lt hL8
    have hHlt := fullEndpointEvenGapCorrection_strictMonoOn hAmem hLmem haL
    change a < L - fullEndpointEvenGapCorrection a
    rw [haeq] at hHlt
    rw [haeq]
    linarith only [hHlt]
  · have hsmall : L - fullEndpointEvenGapCorrection L < 8 := lt_of_not_ge hlarge
    have haeq : a = 8 := by
      dsimp only [a, fullEndpointEvenCorrectionFirstRadius]
      exact max_eq_left (le_of_lt hsmall)
    change a < L - fullEndpointEvenGapCorrection a
    rw [haeq]
    have hH8 : fullEndpointEvenGapCorrection 8 < 7 / 2 := fullEndpointEvenGapCorrection_eight_lt
    linarith only [hL, hH8]

/-- Two fixed substitutions in the correction produce a positive exact gap.
The second radius lies above the first, so strict monotonicity of the
correction makes the affine gap identity positive. -/
theorem fullEndpointEvenTwoStepGap_pos {L : ℝ} (hL : 23 / 2 ≤ L) :
    0 <
      fullEndpointEvenExactComparisonGap L (2096 / 1831) (fullEndpointEvenCorrectionSecondRadius L)
        (Real.log (fullEndpointEvenCorrectionSecondRadius L)) := by
  let a := fullEndpointEvenCorrectionFirstRadius L
  let b := fullEndpointEvenCorrectionSecondRadius L
  have ha8 : 8 ≤ a := by
    dsimp only [a, fullEndpointEvenCorrectionFirstRadius]
    exact le_max_left _ _
  have hab := fullEndpointEvenCorrectionSecondRadius_gt_first hL
  have hb8 : 8 ≤ b := le_trans ha8 hab.le
  have hAmem : a ∈ Set.Ici (8 : ℝ) := ha8
  have hBmem : b ∈ Set.Ici (8 : ℝ) := hb8
  have hHlt := fullEndpointEvenGapCorrection_strictMonoOn hAmem hBmem hab
  have hcor : 0 < fullEndpointEvenGapCorrection b - fullEndpointEvenGapCorrection a :=
    sub_pos.mpr hHlt
  have hgap := fullEndpointEvenExactComparisonGap_eq_denominator_correction (L := L) (y := b) hb8
  rw [hgap]
  have hshape :
    b + fullEndpointEvenGapCorrection b - L =
      fullEndpointEvenGapCorrection b - fullEndpointEvenGapCorrection a := by
    dsimp only [b, fullEndpointEvenCorrectionSecondRadius]
    ring
  rw [hshape]
  exact mul_pos (fullEndpointEvenGapDenominator_pos hb8) hcor

/-- The correction exceeds `16/5` at every radius at least eight. At radius
eight use the anchor estimate; above eight use strict monotonicity. -/
theorem fullEndpointEvenGapCorrection_gt_16over5 {y : ℝ} (hy : 8 ≤ y) :
    (16 / 5 : ℝ) < fullEndpointEvenGapCorrection y := by
  by_cases hEq : y = 8
  · rw [hEq]
    exact fullEndpointEvenGapCorrection_eight_gt
  · have hlt : 8 < y := lt_of_le_of_ne hy (Ne.symm hEq)
    have h8mem : (8 : ℝ) ∈ Set.Ici 8 := by norm_num only [Set.mem_Ici]
    have hymem : y ∈ Set.Ici (8 : ℝ) := hy
    have hmono := fullEndpointEvenGapCorrection_strictMonoOn h8mem hymem hlt
    exact lt_trans fullEndpointEvenGapCorrection_eight_gt hmono

/-- The second corrected radius is less than `L - 16/5`, since its correction
is evaluated at a radius no smaller than eight. -/
theorem fullEndpointEvenCorrectionSecondRadius_lt_linear {L : ℝ} :
    fullEndpointEvenCorrectionSecondRadius L < L - 16 / 5 := by
  have ha8 : 8 ≤ fullEndpointEvenCorrectionFirstRadius L := by
    unfold fullEndpointEvenCorrectionFirstRadius
    exact le_max_left _ _
  have hcor := fullEndpointEvenGapCorrection_gt_16over5 ha8
  unfold fullEndpointEvenCorrectionSecondRadius
  linarith only [hcor]

/-- On the first certified interval, the two-step cutoff improves the shifted
eight-ninths quadratic bound. -/
theorem fullEndpointEvenTwoStepCutoff_lt_shifted_eightNinths {L : ℝ} (hLlo : 23 / 2 ≤ L)
    (hLhi : L ≤ 428 / 25) :
    fullEndpointEvenTwoStepCutoff L < (64 / 81 : ℝ) * (L - 73 / 50) ^ 2 := by
  have hrad := fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L)
  have hcomp : fullEndpointEvenCorrectionSecondRadius L < (8 / 9 : ℝ) * (L - 73 / 50) := by
    nlinarith only [hrad, hLhi]
  have hpos : 0 ≤ fullEndpointEvenCorrectionSecondRadius L := by
    have ha8 : 8 ≤ fullEndpointEvenCorrectionFirstRadius L := by
      unfold fullEndpointEvenCorrectionFirstRadius
      exact le_max_left _ _
    have hab := fullEndpointEvenCorrectionSecondRadius_gt_first hLlo
    linarith only [ha8, hab]
  have htarget : 0 ≤ (8 / 9 : ℝ) * (L - 73 / 50) := by nlinarith only [hLlo]
  have hsquare := (sq_lt_sq₀ hpos htarget).mpr hcomp
  change (fullEndpointEvenCorrectionSecondRadius L) ^ 2 < _
  calc
    (fullEndpointEvenCorrectionSecondRadius L) ^ 2 < ((8 / 9 : ℝ) * (L - 73 / 50)) ^ 2 := hsquare
    _ = (64 / 81 : ℝ) * (L - 73 / 50) ^ 2 := by ring

/-- Up to level `74/5`, the two-step cutoff is also below the earlier shifted
seven-fourths quadratic bound. -/
theorem fullEndpointEvenTwoStepCutoff_lt_shifted_sevenFourths {L : ℝ} (hLlo : 23 / 2 ≤ L)
    (hLhi : L ≤ 74 / 5) : fullEndpointEvenTwoStepCutoff L < (64 / 81 : ℝ) * (L - 7 / 4) ^ 2 := by
  have hrad := fullEndpointEvenCorrectionSecondRadius_lt_linear (L := L)
  have hcomp : fullEndpointEvenCorrectionSecondRadius L < (8 / 9 : ℝ) * (L - 7 / 4) := by
    nlinarith only [hrad, hLhi]
  have hpos : 0 ≤ fullEndpointEvenCorrectionSecondRadius L := by
    have ha8 : 8 ≤ fullEndpointEvenCorrectionFirstRadius L := by
      unfold fullEndpointEvenCorrectionFirstRadius
      exact le_max_left _ _
    have hab := fullEndpointEvenCorrectionSecondRadius_gt_first hLlo
    linarith only [ha8, hab]
  have htarget : 0 ≤ (8 / 9 : ℝ) * (L - 7 / 4) := by nlinarith only [hLlo]
  have hsquare := (sq_lt_sq₀ hpos htarget).mpr hcomp
  change (fullEndpointEvenCorrectionSecondRadius L) ^ 2 < _
  calc
    (fullEndpointEvenCorrectionSecondRadius L) ^ 2 < ((8 / 9 : ℝ) * (L - 7 / 4)) ^ 2 := hsquare
    _ = (64 / 81 : ℝ) * (L - 7 / 4) ^ 2 := by ring

/-- The direct gap at radius twenty-four is positive when the conductor
logarithm is at most `144/5`. -/
theorem fullEndpointEvenExactComparisonGap_pos_at_twentyFour {L : ℝ} (hL : L ≤ 144 / 5) :
    0 < fullEndpointEvenExactComparisonGap L (2096 / 1831) 24 (Real.log 24) := by
  have hlog : (1589 / 500 : ℝ) ≤ Real.log 24 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ^ 3 ≠ 0) (by norm_num only : (3 : ℝ) ≠ 0),
      Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9]
  have hanchor :
    0 < fullEndpointEvenExactComparisonGap (144 / 5) (2096 / 1831) 24 (1589 / 500) := by
    norm_num only [fullEndpointEvenExactComparisonGap]
  have hz := fullEndpointEvenExactComparisonGap_twentyFour_mono_log hlog
  have hlevel :=
    fullEndpointEvenExactComparisonGap_antitone_level (L := L) (K := (144 / 5 : ℝ)) (P :=
      (2096 / 1831 : ℝ)) (y := (24 : ℝ)) (z := Real.log 24) (by norm_num only)
      (Real.log_nonneg (by norm_num only)) hL
  linarith only [hanchor, hz, hlevel]

/-- The shifted even comparison polynomial is monotone in its pi-log parameter.
Only the underlying full-endpoint polynomial depends on that parameter. -/
theorem fullEndpointEvenStarShiftPolynomial_mono_pi {L P Q y z : ℝ} (hy : 1 ≤ y) (hz : 0 ≤ z)
    (hPQ : P ≤ Q) :
    fullEndpointEvenStarShiftPolynomial L P y z ≤ fullEndpointEvenStarShiftPolynomial L Q y z := by
  have hm := fullEndpointPolynomial_mono_pi (L := L + 73 / 50) hy hz hPQ
  unfold fullEndpointEvenStarShiftPolynomial fullEndpointEvenPolynomial
  nlinarith only [hm]

/-- At equal squared cutoffs, the even endpoint limit is represented by the
parity-refined polynomial. Clear the endpoint denominator after simplifying the
square root and logarithm. -/
theorem fullEndpointEvenPolynomial_eq_neg_limit (q : ℕ) {y : ℝ} (hy : 1 < y) :
    -(y * (y - 1) ^ 2) * reciprocalGapFullEndpointEvenLimit q (y ^ 2) (y ^ 2) =
      fullEndpointEvenPolynomial (Real.log q) (Real.log Real.pi) y (Real.log y) := by
  have hy0 : y ≠ 0 := (zero_lt_one.trans hy).ne'
  have hy1 : y - 1 ≠ 0 := (sub_pos.mpr hy).ne'
  unfold reciprocalGapFullEndpointEvenLimit reciprocalGapEvenReciprocalMassCap
    fullEndpointEvenPolynomial fullEndpointPolynomial
  rw [Real.sqrt_inv, Real.sqrt_sq (zero_lt_one.trans hy).le, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  field_simp [hy0, hy1]
  ring

/-- For every `y >= 8`, shifting the ordinary endpoint level by `9/8` and using
the even mass cap strictly improves the polynomial. The difference is bounded
below by a positive cubic in `y - 8`; hence this transfer is uniform on the full
half-line and needs no interval certificate. -/
theorem fullEndpointPolynomial_lt_even_shift {L P y : ℝ} (hy : 8 ≤ y) :
    fullEndpointPolynomial L P y (Real.log y) <
      fullEndpointEvenPolynomial (L + 9 / 8) P y (Real.log y) := by
  have hd :
    fullEndpointEvenPolynomial (L + 9 / 8) P y (Real.log y) -
        fullEndpointPolynomial L P y (Real.log y) =
      (129 / 100 : ℝ) * y ^ 2 * (y + Real.log y + 1) -
        (9 / 8 : ℝ) * (y - 1) * ((y + 1) ^ 2 + 2 * y * Real.log y) := by
    dsimp only [fullEndpointEvenPolynomial]
    unfold fullEndpointPolynomial
    ring
  have hy0 : 0 < y := by linarith only [hy]
  have ht := Analysis.log_le_log_add_sub_div (a := (8 : ℝ)) (y := y) (by norm_num only) hy0
  have he8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlog : Real.log y ≤ y / 8 + 11 / 10 := by
    rw [he8] at ht
    linarith only [ht, Real.log_two_lt_d9]
  have hu : 0 ≤ y - 8 := by linarith only [hy]
  have hbound :
    (13941 / 1000 : ℝ) + (621 / 250) * (y - 8) + (1881 / 4000) * (y - 8) ^ 2 +
        (9 / 200) * (y - 8) ^ 3 ≤
      (129 / 100 : ℝ) * y ^ 2 * (y + Real.log y + 1) -
        (9 / 8 : ℝ) * (y - 1) * ((y + 1) ^ 2 + 2 * y * Real.log y) := by
    nlinarith only [hlog, hu, sq_nonneg (y - 8), pow_nonneg hu 3]
  have hpos :
    0 <
      (13941 / 1000 : ℝ) + (621 / 250) * (y - 8) + (1881 / 4000) * (y - 8) ^ 2 +
        (9 / 200) * (y - 8) ^ 3 := by
    nlinarith only [hu, sq_nonneg (y - 8), pow_nonneg hu 3]
  rw [← sub_pos, hd]
  linarith only [hbound, hpos]

/-- For every `y >= 8`, the ordinary endpoint polynomial lies strictly below
the corrected even polynomial at shift `73/50`. Expand at `y=8` and `log y=2`;
all coefficients of the resulting polynomial in the two nonnegative offsets are positive. -/
theorem fullEndpointPolynomial_lt_even_star_shift {L P y : ℝ} (hy : 8 ≤ y) :
    fullEndpointPolynomial L P y (Real.log y) <
      fullEndpointEvenStarShiftPolynomial L P y (Real.log y) := by
  let u := y - 8
  let v := Real.log y - 2
  have hu : 0 ≤ u := by
    dsimp only [u]; linarith only [hy]
  have hv : 0 ≤ v := by
    have hlog8 : 2 ≤ Real.log 8 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [Real.log_two_gt_d9]
    have hlog := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hy
    dsimp only [v]
    linarith only [hlog, hlog8]
  have hd :
    fullEndpointEvenStarShiftPolynomial L P y (Real.log y) -
        fullEndpointPolynomial L P y (Real.log y) =
      (364959 / 1000 : ℝ) + (24769 / 200) * u + (9507 / 1000) * u ^ 2 + (1 / 1000) * u ^ 3 +
        ((277209 / 1000 : ℝ) + (11297 / 125) * u + (6741 / 1000) * u ^ 2) * v +
        (94 + 28 * u + 2 * u ^ 2) * v ^ 2 := by
    dsimp only [fullEndpointEvenStarShiftPolynomial, fullEndpointEvenPolynomial,
      fullEndpointPolynomial, u, v]
    ring
  have hpositive :
    0 <
      (364959 / 1000 : ℝ) + (24769 / 200) * u + (9507 / 1000) * u ^ 2 + (1 / 1000) * u ^ 3 +
        ((277209 / 1000 : ℝ) + (11297 / 125) * u + (6741 / 1000) * u ^ 2) * v +
        (94 + 28 * u + 2 * u ^ 2) * v ^ 2 := by
    positivity
  rw [← sub_pos, hd]
  exact hpositive

/-- Increasing the star-shift input from `L` to `L + 29/100` adds a further
`29/100` to the embedded `73/50`, giving the total level shift `7/4`. The
comparison is monotone in the logarithmic radius once its lower endpoint is at
least two. -/
theorem fullEndpointPolynomial_lt_even_star_shift_7over4_of_log_lower {L P y z z0 : ℝ} (hy : 8 ≤ y)
    (hz0 : 2 ≤ z0) (hz : z0 ≤ z)
    (hgap :
      0 <
        fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 -
          fullEndpointPolynomial L P y z0) :
    fullEndpointPolynomial L P y z < fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z := by
  have hdiff (w : ℝ) :
    fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y w - fullEndpointPolynomial L P y w =
      -(289 / 1000 : ℝ) * y ^ 3 + (3711 / 1000) * y ^ 2 - (353 / 40) * y + 127 / 40 +
        (2 * y ^ 2 - 4 * y - 2) * w ^ 2 +
        (-(1839 / 1000) * y ^ 2 - 9 / 10 * y - 51 / 8) * w := by
    unfold fullEndpointEvenStarShiftPolynomial fullEndpointEvenPolynomial fullEndpointPolynomial
    ring
  let A : ℝ := 2 * y ^ 2 - 4 * y - 2
  let B : ℝ := 1839 / 1000 * y ^ 2 + 9 / 10 * y + 51 / 8
  have hA : y ^ 2 ≤ A := by
    dsimp only [A]; nlinarith only [hy]
  have hAnonneg : 0 ≤ A := le_trans (sq_nonneg y) hA
  have hprodA : 4 * A ≤ A * (z + z0) := by
    calc
      4 * A = A * 4 := by ring
      _ ≤ A * (z + z0) :=
        mul_le_mul_of_nonneg_left (by linarith only [hz0, hz] : 4 ≤ z + z0) hAnonneg
  have hprod : 4 * y ^ 2 ≤ A * (z + z0) := by nlinarith only [hprodA, hA]
  have hysq : 64 ≤ y ^ 2 := by nlinarith only [hy]
  have hyline : 8 * y ≤ y ^ 2 := by nlinarith only [hy]
  have hsmall : B ≤ 3 * y ^ 2 := by
    dsimp only [B]
    nlinarith only [hysq, hyline]
  have hfactor : 0 ≤ A * (z + z0) - B := by nlinarith only [hprod, hsmall]
  have hgapDiff : 0 ≤ (A * z ^ 2 - B * z) - (A * z0 ^ 2 - B * z0) := by
    calc
      _ = (z - z0) * (A * (z + z0) - B) := by ring
      _ ≥ 0 := mul_nonneg (sub_nonneg.mpr hz) hfactor
  have hQ :
    0 <
      fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z -
        fullEndpointPolynomial L P y z := by
    rw [hdiff z]
    have hgap0 := hgap
    rw [hdiff z0] at hgap0
    dsimp only [A, B] at hgapDiff ⊢
    nlinarith only [hgap0, hgapDiff]
  exact sub_pos.mp hQ

/-- On radii from eight through sixteen, the rational lower bound `2079/1000`
for the logarithm certifies the `7/4` endpoint shift. -/
theorem fullEndpointPolynomial_lt_even_star_shift_7over4_eight_to_sixteen {L P y z : ℝ}
    (hy8 : 8 ≤ y) (hy16 : y ≤ 16) (hz : 2079 / 1000 ≤ z) :
    fullEndpointPolynomial L P y z < fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z := by
  let z0 : ℝ := 2079 / 1000
  let u : ℝ := y - 8
  have hu0 : 0 ≤ u := by
    dsimp only [u]; linarith only [hy8]
  have hu8 : u ≤ 8 := by
    dsimp only [u]; linarith only [hy16]
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos (lt_of_lt_of_le (by norm_num only) hy8)
  have hpoly :
    0 <
      y ^ 2 *
        (fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 -
          fullEndpointPolynomial L P y z0) := by
    have hid :
      y ^ 2 *
          (fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 -
            fullEndpointPolynomial L P y z0) =
        -(289 / 1000 : ℝ) * u ^ 5 - (3027799 / 1000000) * u ^ 4 + (7510671 / 125000) * u ^ 3 +
          (1106320541 / 1000000) * u ^ 2 +
          (367657853 / 62500) * u +
          31097849 / 3125 := by
      dsimp only [u, z0]
      unfold fullEndpointEvenStarShiftPolynomial fullEndpointEvenPolynomial fullEndpointPolynomial
      ring
    have hu5 : u ^ 5 ≤ 8 * u ^ 4 := by
      calc
        u ^ 5 = u ^ 4 * u := by ring
        _ ≤ u ^ 4 * 8 := mul_le_mul_of_nonneg_left hu8 (pow_nonneg hu0 4)
        _ = 8 * u ^ 4 := by ring
    have hu4 : u ^ 4 ≤ 8 * u ^ 3 := by
      calc
        u ^ 4 = u ^ 3 * u := by ring
        _ ≤ u ^ 3 * 8 := mul_le_mul_of_nonneg_left hu8 (pow_nonneg hu0 3)
        _ = 8 * u ^ 3 := by ring
    rw [hid]
    nlinarith only [hu0, hu5, hu4]
  have hgap :
    0 <
      fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 - fullEndpointPolynomial L P y z0 :=
    (mul_pos_iff_of_pos_left hy2).mp hpoly
  apply
    fullEndpointPolynomial_lt_even_star_shift_7over4_of_log_lower hy8
      (by
        dsimp only [z0]; norm_num only)
      (by
        dsimp only [z0]; linarith only [hz])
      hgap

/-- On radii from sixteen through sixty-four, the lower estimate
`log y >= log 32 + 1 - 32/y` certifies the `7/4` endpoint shift. -/
theorem fullEndpointPolynomial_lt_even_star_shift_7over4_sixteen_to_sixtyFour {L P y z : ℝ}
    (hy16 : 16 ≤ y) (hy64 : y ≤ 64) (hz : 4465 / 1000 - 32 / y ≤ z) :
    fullEndpointPolynomial L P y z < fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z := by
  let z0 : ℝ := 4465 / 1000 - 32 / y
  let u : ℝ := y - 16
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy16
  have hdiv : 32 / y ≤ 2 := (div_le_iff₀ hypos).2 (by nlinarith only [hy16])
  have hz02 : 2 ≤ z0 := by
    dsimp only [z0]; norm_num only; linarith only [hdiv]
  have hu0 : 0 ≤ u := by
    dsimp only [u]; linarith only [hy16]
  have hu48 : u ≤ 48 := by
    dsimp only [u]; linarith only [hy64]
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hypos
  have hpoly :
    0 <
      y ^ 2 *
        (fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 -
          fullEndpointPolynomial L P y z0) := by
    have hid :
      y ^ 2 *
          (fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 -
            fullEndpointPolynomial L P y z0) =
        -(289 / 1000 : ℝ) * u ^ 5 + (2450463 / 200000) * u ^ 4 + (11484097 / 12500) * u ^ 3 +
          (3319322963 / 200000) * u ^ 2 +
          (735185771 / 6250) * u +
          901240332 / 3125 := by
      dsimp only [u, z0]
      unfold fullEndpointEvenStarShiftPolynomial fullEndpointEvenPolynomial fullEndpointPolynomial
      field_simp [ne_of_gt hypos]
      ring
    have hu5 : u ^ 5 ≤ 48 * u ^ 4 := by
      calc
        u ^ 5 = u ^ 4 * u := by ring
        _ ≤ u ^ 4 * 48 := mul_le_mul_of_nonneg_left hu48 (pow_nonneg hu0 4)
        _ = 48 * u ^ 4 := by ring
    have hu4 : u ^ 4 ≤ 48 * u ^ 3 := by
      calc
        u ^ 4 = u ^ 3 * u := by ring
        _ ≤ u ^ 3 * 48 := mul_le_mul_of_nonneg_left hu48 (pow_nonneg hu0 3)
        _ = 48 * u ^ 3 := by ring
    rw [hid]
    nlinarith only [hu0, hu5, hu4]
  have hgap :
    0 <
      fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 - fullEndpointPolynomial L P y z0 :=
    (mul_pos_iff_of_pos_left hy2).mp hpoly
  exact
    fullEndpointPolynomial_lt_even_star_shift_7over4_of_log_lower (by linarith only [hy16]) hz02
      (by
        dsimp only [z0]; linarith only [hz])
      hgap

/-- On radii from sixty-four through 128, the lower estimate
`log y >= log 128 + 1 - 128/y` certifies the `7/4` endpoint shift. -/
theorem fullEndpointPolynomial_lt_even_star_shift_7over4_sixtyFour_to_oneTwentyEight {L P y z : ℝ}
    (hy64 : 64 ≤ y) (hy128 : y ≤ 128) (hz : 5851 / 1000 - 128 / y ≤ z) :
    fullEndpointPolynomial L P y z < fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z := by
  let z0 : ℝ := 5851 / 1000 - 128 / y
  let u : ℝ := y - 64
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy64
  have hdiv : 128 / y ≤ 2 := (div_le_iff₀ hypos).2 (by nlinarith only [hy64])
  have hz02 : 2 ≤ z0 := by
    dsimp only [z0]; norm_num only; linarith only [hdiv]
  have hu0 : 0 ≤ u := by
    dsimp only [u]; linarith only [hy64]
  have hu64 : u ≤ 64 := by
    dsimp only [u]; linarith only [hy128]
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hypos
  have hpoly :
    0 <
      y ^ 2 *
        (fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 -
          fullEndpointPolynomial L P y z0) := by
    have hid :
      y ^ 2 *
          (fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 -
            fullEndpointPolynomial L P y z0) =
        -(289 / 1000 : ℝ) * u ^ 5 - (31060587 / 1000000) * u ^ 4 + (121822753 / 125000) * u ^ 3 +
          (231640605193 / 1000000) * u ^ 2 +
          (29019688474 / 3125) * u +
          349281728832 / 3125 := by
      dsimp only [u, z0]
      unfold fullEndpointEvenStarShiftPolynomial fullEndpointEvenPolynomial fullEndpointPolynomial
      field_simp [ne_of_gt hypos]
      ring
    have hu5 : u ^ 5 ≤ 64 * u ^ 4 := by
      calc
        u ^ 5 = u ^ 4 * u := by ring
        _ ≤ u ^ 4 * 64 := mul_le_mul_of_nonneg_left hu64 (pow_nonneg hu0 4)
        _ = 64 * u ^ 4 := by ring
    have hu4 : u ^ 4 ≤ 64 * u ^ 3 := by
      calc
        u ^ 4 = u ^ 3 * u := by ring
        _ ≤ u ^ 3 * 64 := mul_le_mul_of_nonneg_left hu64 (pow_nonneg hu0 3)
        _ = 64 * u ^ 3 := by ring
    have hu3 : u ^ 3 ≤ 64 * u ^ 2 := by
      calc
        u ^ 3 = u ^ 2 * u := by ring
        _ ≤ u ^ 2 * 64 := mul_le_mul_of_nonneg_left hu64 (pow_nonneg hu0 2)
        _ = 64 * u ^ 2 := by ring
    rw [hid]
    nlinarith only [hu0, hu5, hu4, hu3]
  have hgap :
    0 <
      fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y z0 - fullEndpointPolynomial L P y z0 :=
    (mul_pos_iff_of_pos_left hy2).mp hpoly
  exact
    fullEndpointPolynomial_lt_even_star_shift_7over4_of_log_lower (by linarith only [hy64]) hz02
      (by
        dsimp only [z0]; linarith only [hz])
      hgap

/-- For `16 ≤ y ≤ 64`, derive the rational logarithm lower bound used by the
middle scale band from `log y ≥ log 32 + 1 - 32/y`. -/
theorem log_lower_sixteen_to_sixtyFour {y : ℝ} (hy16 : 16 ≤ y) :
    4465 / 1000 - 32 / y ≤ Real.log y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy16
  have hratio := Real.log_le_sub_one_of_pos (div_pos (by norm_num only : (0 : ℝ) < 32) hypos)
  rw [Real.log_div (by norm_num only : (32 : ℝ) ≠ 0) hypos.ne'] at hratio
  have hlog32 : (3465 / 1000 : ℝ) ≤ Real.log 32 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hlog : Real.log 32 + 1 - 32 / y ≤ Real.log y := by linarith only [hratio]
  linarith only [hlog32, hlog]

/-- For `64 ≤ y ≤ 128`, derive the rational logarithm lower bound used by the
large scale band from `log y ≥ log 128 + 1 - 128/y`. -/
theorem log_lower_sixtyFour_to_oneTwentyEight {y : ℝ} (hy64 : 64 ≤ y) :
    5851 / 1000 - 128 / y ≤ Real.log y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num only) hy64
  have hratio := Real.log_le_sub_one_of_pos (div_pos (by norm_num only : (0 : ℝ) < 128) hypos)
  rw [Real.log_div (by norm_num only : (128 : ℝ) ≠ 0) hypos.ne'] at hratio
  have hlog128 : (4851 / 1000 : ℝ) ≤ Real.log 128 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_gt_d9]
  have hlog : Real.log 128 + 1 - 128 / y ≤ Real.log y := by linarith only [hratio]
  linarith only [hlog128, hlog]

/-- The `7/4` shifted endpoint polynomial dominates the unshifted polynomial
throughout the certified practical radius range `8 ≤ y ≤ 128`. -/
theorem fullEndpointPolynomial_lt_even_star_shift_7over4_of_radius_range {L P y : ℝ} (hy8 : 8 ≤ y)
    (hy128 : y ≤ 128) :
    fullEndpointPolynomial L P y (Real.log y) <
      fullEndpointEvenStarShiftPolynomial (L + 29 / 100) P y (Real.log y) := by
  by_cases hy16 : y ≤ 16
  · have hlog8 : (2079 / 1000 : ℝ) ≤ Real.log 8 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_gt_d9]
    have hlogy : Real.log 8 ≤ Real.log y := Real.log_le_log (by norm_num only : (0 : ℝ) < 8) hy8
    exact
      fullEndpointPolynomial_lt_even_star_shift_7over4_eight_to_sixteen hy8 hy16
        (le_trans hlog8 hlogy)
  · have hy16 : 16 ≤ y := le_of_not_ge hy16
    by_cases hy64 : y ≤ 64
    · have hlog := log_lower_sixteen_to_sixtyFour hy16
      exact fullEndpointPolynomial_lt_even_star_shift_7over4_sixteen_to_sixtyFour hy16 hy64 hlog
    · have hy64 : 64 ≤ y := le_of_not_ge hy64
      have hlog := log_lower_sixtyFour_to_oneTwentyEight hy64
      exact
        fullEndpointPolynomial_lt_even_star_shift_7over4_sixtyFour_to_oneTwentyEight hy64 hy128 hlog

/-- If every prime through `x` has character value one, the real logarithmic
character sum equals the unsigned Mangoldt sum. Apply the full-prime-triviality
identity with logarithmic weights. -/
theorem logWeightedSum_re_eq_of_full_prime_trivial {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 ≤ x) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) :
    (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ).re =
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x := by
  have hs :=
    AnalyticNumberTheory.Arithmetic.weighted_sum_re_eq_of_full_prime_trivial χ ht
      (Finset.Ioc 0 ⌊x⌋₊)
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx))
      (fun n ↦ Real.log (x / n))
  unfold AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
    AnalyticNumberTheory.Arithmetic.characterLogWeightedTerm
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (χ n).re * ArithmeticFunction.vonMangoldt n * Real.log (x / n) :=
      by
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = _ := hs

/-- For a primitive even nonprincipal character under GRH, positivity of the
direct comparison gap at the rational pi-log lower bound yields a non-one prime through `y^2`.
Assume all such primes are trivial, apply the exact reciprocal and logarithmic
bounds, and contradict the refined Riemann lower bound directly. -/
theorem exists_prime_not_one_of_positive_exact_even_endpoint_gap {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {y : ℝ} (hy : 8 ≤ y)
    (hgapPositive :
      0 < fullEndpointEvenExactComparisonGap (Real.log q) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  by_contra hn
  have hypos : 0 < y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y)
  have hy2 : 64 ≤ y ^ 2 := by nlinarith only [hy]
  have hx : 1 < y ^ 2 := by nlinarith only [hy]
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ y ^ 2 → χ p = 1 := by
    intro p hprime hpy
    by_contra hv
    exact hn ⟨p, hprime, hpy, hv⟩
  have hRecId := reciprocalSum_re_eq_of_full_prime_trivial χ (by positivity : 0 ≤ y ^ 2) ht
  have hRecLower :=
    AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 (x :=
      y ^ 2) hGRH.riemann (by linarith only [hy2])
  rw [← hRecId] at hRecLower
  rw [Real.log_pow] at hRecLower
  have hError := Analysis.primitiveReciprocalEvenMainError_le_exact_even_envelope hy
  have hRaw :=
    PseudoPrime.LLS.primitiveReciprocalRaw_even_le_of_mainError hq hGRH hp hne hinv heven
      (by linarith only [hx]) hError
  rw [Real.sqrt_sq (by linarith only [hy] : 0 ≤ y)] at hRaw
  have hrec :
    2 * Real.log y - 31551 / 20000 ≤
      (1 / 2 : ℝ) * (1 - 1 / y ^ 2) * (Real.log q - Real.log Real.pi) - 1961 / 2000 +
          (2 * Real.log y + 103 / 80) / y ^ 2 -
        (1 - 1 / y) ^ 2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
    nlinarith only [hRecLower, hRaw]
  have hpi0 : Real.pi < (31416 / 10000 : ℝ) := by
    calc
      Real.pi < 3.1416 := Real.pi_lt_d4
      _ = (31416 / 10000 : ℝ) := by norm_num only
  have hpi2 : Real.pi ^ 2 / 24 ≤ (103 / 250 : ℝ) := by
    have hsq : Real.pi ^ 2 ≤ (31416 / 10000 : ℝ) ^ 2 := by nlinarith only [Real.pi_pos, hpi0]
    nlinarith only [hsq]
  have hgamma : (23 / 40 : ℝ) ≤ Real.eulerMascheroniConstant :=
    Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant.le
  have hMain :
    Analysis.primitiveLogEvenMainError (y ^ 2) ≤
      103 / 250 - (23 / 40) * Real.log y - 2 * (Real.log y) ^ 2 := by
    unfold Analysis.primitiveLogEvenMainError
    rw [Real.log_pow]
    nlinarith only [hpi2, hgamma, hz]
  have hLog :=
    AnalyticNumberTheory.DirichletLFunction.primitiveLogWeightedUpper_of_grh_even_exact (x := y ^ 2)
      hq hGRH hp hne hinv heven hy2
  rw [Real.sqrt_sq (by linarith only [hy] : 0 ≤ y), Real.log_pow] at hLog
  have hLogId := logWeightedSum_re_eq_of_full_prime_trivial χ (by positivity : 0 ≤ y ^ 2) ht
  rw [hLogId] at hLog
  have hupper :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2) ≤
      (2 * y + 2 + 2 * Real.log y) * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
          (Real.log q - Real.log Real.pi) * Real.log y +
          103 / 250 -
        (23 / 40) * Real.log y -
        2 * (Real.log y) ^ 2 := by
    nlinarith only [hLog, hMain]
  have hlower := PseudoPrime.LLS.logWeightedMangoldtSum_ge_rational_refined hGRH.riemann hx
  rw [Real.sqrt_sq (by linarith only [hy] : 0 ≤ y), Real.log_pow] at hlower
  have hlower' :
    y ^ 2 - y / 20 - (1839 / 500 : ℝ) * Real.log y - 21 / 20 ≤
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2) := by
    nlinarith only [hlower]
  have hgap :=
    fullEndpointEvenExactComparisonGap_nonpos hy hz hrec hupper hlower' (L := Real.log q) (P :=
      Real.log Real.pi) (y := y) (z := Real.log y) (B :=
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ|) (S :=
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (y ^ 2))
  have hgapPi :=
    fullEndpointEvenExactComparisonGap_mono_pi (L := Real.log q) (P := (2096 / 1831 : ℝ)) (Q :=
      Real.log Real.pi) (y := y) (z := Real.log y) (by linarith only [hy]) hz
      Analysis.log_pi_ge_2096_div_1831
  linarith only [hgap, hgapPositive, hgapPi]

/-- The shifted even endpoint polynomial criterion is a specialization of the
direct-gap witness consumer. The polynomial transfers to the even comparison
polynomial, which is bounded above by the exact gap. -/
theorem exists_prime_not_one_of_exact_even_endpoint_polynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {y : ℝ} (hy : 8 ≤ y)
    (hpoly : 0 < fullEndpointPolynomial (Real.log q - 73 / 50) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  have htransfer :=
    fullEndpointPolynomial_lt_even_star_shift hy (L := Real.log q - 73 / 50) (P :=
      (2096 / 1831 : ℝ))
  have hstar :
    0 < fullEndpointEvenStarShiftPolynomial (Real.log q - 73 / 50) (2096 / 1831) y (Real.log y) :=
    lt_trans hpoly htransfer
  have hbridge :=
    fullEndpointEvenStarShiftPolynomial_le_exact_comparison_gap (L := Real.log q) (P :=
      (2096 / 1831 : ℝ)) (y := y) (z := Real.log y) (by linarith only [hy] : y ≠ 0)
      (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y))
      (by norm_num only : (9 / 8 : ℝ) ≤ 2096 / 1831)
  have hgap : 0 < fullEndpointEvenExactComparisonGap (Real.log q) (2096 / 1831) y (Real.log y) :=
    lt_of_lt_of_le hstar hbridge
  exact exists_prime_not_one_of_positive_exact_even_endpoint_gap χ hq hGRH hp hne hinv heven hy hgap

/-- The exact even endpoint criterion applies to an arbitrary nonprincipal even
character. Move its conductor logarithm below the ambient level in the polynomial,
then transfer the prime witness from the primitive character. -/
theorem exists_prime_ne_one_of_exact_even_endpoint_polynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hpoly : 0 < fullEndpointPolynomial (Real.log q - 73 / 50) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)⟩
  have hcond : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hlog : Real.log χ.conductor ≤ Real.log q :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr hcond)
  have hpoly' :
    0 < fullEndpointPolynomial (Real.log χ.conductor - 73 / 50) (2096 / 1831) y (Real.log y) := by
    have hm :=
      fullEndpointPolynomial_antitone_level (L := Real.log χ.conductor - 73 / 50) (K :=
        Real.log q - 73 / 50) (P := (2096 / 1831 : ℝ)) (y := y) (z := Real.log y)
        (by linarith only [hy]) (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y))
        (sub_le_sub_right hlog (73 / 50))
    linarith only [hpoly, hm]
  obtain ⟨p, hp, hpy, hv⟩ :=
    exists_prime_not_one_of_exact_even_endpoint_polynomial χ.primitiveCharacter hq hGRH
      χ.primitiveCharacter_isPrimitive hψ (inv_ne_one.mpr hψ)
      (reciprocalGap_primitiveCharacter_even heven) hy hpoly'
  refine ⟨p, hp, hpy, ?_⟩
  intro hone
  exact hv (primitiveCharacter_apply_one_of_apply_one χ hone)

/-- A positive direct endpoint gap at the ambient level transfers to the
primitive conductor and produces a non-one prime for any even nonprincipal
character. -/
theorem exists_prime_ne_one_of_positive_exact_even_endpoint_gap {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hgap : 0 < fullEndpointEvenExactComparisonGap (Real.log q) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)⟩
  have hcond : χ.conductor ≤ q := Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have hlog : Real.log χ.conductor ≤ Real.log q :=
    Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero χ.conductor_ne_zero))
      (Nat.cast_le.mpr hcond)
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hz : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hgapCond :
    0 < fullEndpointEvenExactComparisonGap (Real.log χ.conductor) (2096 / 1831) y (Real.log y) := by
    have hmono :=
      fullEndpointEvenExactComparisonGap_antitone_level (L := Real.log χ.conductor) (K :=
        Real.log q) (P := (2096 / 1831 : ℝ)) (y := y) (z := Real.log y) hy1 hz hlog
    exact lt_of_lt_of_le hgap hmono
  obtain ⟨p, hp, hpy, hv⟩ :=
    exists_prime_not_one_of_positive_exact_even_endpoint_gap χ.primitiveCharacter hq hGRH
      χ.primitiveCharacter_isPrimitive hψ (inv_ne_one.mpr hψ)
      (reciprocalGap_primitiveCharacter_even heven) hy hgapCond
  refine ⟨p, hp, hpy, ?_⟩
  intro hone
  exact hv (primitiveCharacter_apply_one_of_apply_one χ hone)

/-- A positive ordinary endpoint polynomial at level `log q - 7/4` gives a
non-one prime through `y^2` when `8 ≤ y ≤ 128`. The three certified scale bands
transfer that polynomial to the direct exact gap at the ambient level. -/
theorem exists_prime_ne_one_of_7over4_shifted_endpoint_polynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hy128 : y ≤ 128)
    (hpoly : 0 < fullEndpointPolynomial (Real.log q - 7 / 4) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  have htransfer :=
    fullEndpointPolynomial_lt_even_star_shift_7over4_of_radius_range (L := Real.log q - 7 / 4) (P :=
      (2096 / 1831 : ℝ)) hy hy128
  have hstar :
    0 <
      fullEndpointEvenStarShiftPolynomial (Real.log q - 73 / 50) (2096 / 1831) y (Real.log y) := by
    have heq : Real.log q - 7 / 4 + 29 / 100 = Real.log q - 73 / 50 := by ring
    rw [← heq]
    exact lt_trans hpoly htransfer
  have hbridge :=
    fullEndpointEvenStarShiftPolynomial_le_exact_comparison_gap (L := Real.log q) (P :=
      (2096 / 1831 : ℝ)) (y := y) (z := Real.log y) (by linarith only [hy] : y ≠ 0)
      (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y))
      (by norm_num only : (9 / 8 : ℝ) ≤ 2096 / 1831)
  have hgap : 0 < fullEndpointEvenExactComparisonGap (Real.log q) (2096 / 1831) y (Real.log y) :=
    lt_of_lt_of_le hstar hbridge
  exact exists_prime_ne_one_of_positive_exact_even_endpoint_gap χ hne heven hGRH hy hgap

/-- On the certified five-piece interval while its radius is at most 128, the
seven-fourths shifted level yields the improved affine-radius witness bound. -/
theorem exists_prime_ne_one_le_7over4_shifted_midscale_radius_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 144 / 5 ≤ Real.log q)
    (hLhi : Real.log q ≤ 13517 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (midscaleEndpointRadius (Real.log q - 7 / 4)) ^ 2 ∧ χ p ≠ 1 := by
  let L := Real.log q - 7 / 4
  have hLlo' : 1339 / 50 ≤ L := by
    dsimp only [L]; nlinarith only [hLlo]
  have hLhi' : L ≤ 6671 / 50 := by
    dsimp only [L]; nlinarith only [hLhi]
  have hdata := midscaleEndpointRadius_data hLlo' (by linarith only [hLhi'])
  have hy128 := midscaleEndpointRadius_le_128 hLhi'
  have hy8 : 8 ≤ midscaleEndpointRadius L := by linarith only [hdata.1]
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_7over4_shifted_endpoint_polynomial χ hne heven hGRH hy8 hy128 hdata.2
  exact ⟨p, hp, hb, hv⟩

/-- The bounded seven-fourths transfer gives the `64/81` quadratic witness
bound from logarithmic scale `43/4` through `22`. -/
theorem exists_prime_ne_one_le_7over4_shifted_eightNinths_log_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 43 / 4 ≤ Real.log q)
    (hLhi : Real.log q ≤ 22) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log q - 7 / 4) ^ 2 ∧ χ p ≠ 1 := by
  let X := Real.log q - 7 / 4
  have hXlo : 9 ≤ X := by
    dsimp only [X]; linarith only [hLlo]
  have hXhi : X ≤ 81 / 4 := by
    dsimp only [X]; linarith only [hLhi]
  have hy : (8 : ℝ) ≤ (8 / 9 : ℝ) * X := by nlinarith only [hXlo]
  have hy128 : (8 / 9 : ℝ) * X ≤ 128 := by nlinarith only [hXhi]
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_7over4_shifted_endpoint_polynomial χ hne heven hGRH hy hy128
      (fullEndpoint_polynomial_pos_eightNinths_log_interval hXlo hXhi)
  refine ⟨p, hp, ?_, hv⟩
  dsimp only [X] at hb ⊢
  nlinarith only [hb]

/-- The bounded seven-fourths transfer gives the `81/100` quadratic witness
bound from logarithmic scale `43/4` through `111/4`. -/
theorem exists_prime_ne_one_le_7over4_shifted_eightyOne_log_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 43 / 4 ≤ Real.log q)
    (hLhi : Real.log q ≤ 111 / 4) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log q - 7 / 4) ^ 2 ∧ χ p ≠ 1 := by
  let X := Real.log q - 7 / 4
  have hXlo : 9 ≤ X := by
    dsimp only [X]; linarith only [hLlo]
  have hXhi : X ≤ 26 := by
    dsimp only [X]; linarith only [hLhi]
  have hy : (8 : ℝ) ≤ (9 / 10 : ℝ) * X := by nlinarith only [hXlo]
  have hy128 : (9 / 10 : ℝ) * X ≤ 128 := by nlinarith only [hXhi]
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_of_7over4_shifted_endpoint_polynomial χ hne heven hGRH hy hy128
      (fullEndpoint_polynomial_pos_eightyOne_log_interval hXlo hXhi)
  refine ⟨p, hp, ?_, hv⟩
  dsimp only [X] at hb ⊢
  nlinarith only [hb]

/-- The ordinary endpoint polynomial at radius 24 stays positive below the
midscale entrance level. Anchor the inequality at the certified radius 24 and
use antitonicity in the conductor logarithm. -/
theorem fullEndpoint_polynomial_pos_at_twentyFour_of_level_le {L : ℝ} (hL : L ≤ 1339 / 50) :
    0 < fullEndpointPolynomial L (2096 / 1831) 24 (Real.log 24) := by
  have hbase :=
    midscaleEndpointRadius_data (L := (1339 / 50 : ℝ)) (by norm_num only) (by norm_num only)
  have hr : midscaleEndpointRadius (1339 / 50) = 24 := by
    unfold midscaleEndpointRadius
    norm_num
  have hp0 : 0 < fullEndpointPolynomial (1339 / 50) (2096 / 1831) 24 (Real.log 24) := by
    rw [← hr]
    exact hbase.2
  have hm :=
    fullEndpointPolynomial_antitone_level (P := (2096 / 1831 : ℝ)) (y := (24 : ℝ)) (z :=
      Real.log 24) (by norm_num only) (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 24)) hL
  exact lt_of_lt_of_le hp0 hm

/-- A positive shifted ordinary polynomial gives a negative even endpoint limit.
The uniform radius transfer pays a level shift of `9/8`; monotonicity in the
pi-log parameter then replaces the certified rational lower bound by `log pi`. -/
theorem fullEndpointEvenLimit_neg_of_shifted_rational_polynomial_pos (q : ℕ) {y : ℝ} (hy : 8 ≤ y)
    (hpoly : 0 < fullEndpointPolynomial (Real.log q - 9 / 8) (2096 / 1831) y (Real.log y)) :
    reciprocalGapFullEndpointEvenLimit q (y ^ 2) (y ^ 2) < 0 := by
  have htransfer :=
    fullEndpointPolynomial_lt_even_shift hy (L := Real.log q - 9 / 8) (P := (2096 / 1831 : ℝ))
  have hpos : 0 < fullEndpointEvenPolynomial (Real.log q) (2096 / 1831) y (Real.log y) := by
    have heq : Real.log q - 9 / 8 + 9 / 8 = Real.log q := by ring
    rw [← heq]
    exact lt_trans hpoly htransfer
  have hm :=
    fullEndpointPolynomial_mono_pi (L := Real.log q) (P := (2096 / 1831 : ℝ)) (Q :=
      Real.log Real.pi) (y := y) (z := Real.log y) (by linarith only [hy])
      (Real.log_nonneg (by linarith only [hy] : (1 : ℝ) ≤ y)) Analysis.log_pi_ge_2096_div_1831
  have he : 0 < fullEndpointEvenPolynomial (Real.log q) (Real.log Real.pi) y (Real.log y) := by
    have hme :
      fullEndpointEvenPolynomial (Real.log q) (2096 / 1831) y (Real.log y) ≤
        fullEndpointEvenPolynomial (Real.log q) (Real.log Real.pi) y (Real.log y) := by
      unfold fullEndpointEvenPolynomial
      nlinarith only [hm]
    linarith only [hpos, hme]
  have hid := fullEndpointEvenPolynomial_eq_neg_limit q (by linarith only [hy] : 1 < y)
  have hc : 0 < y * (y - 1) ^ 2 :=
    mul_pos (by linarith only [hy]) (sq_pos_of_pos (by linarith only [hy]))
  nlinarith only [hid, he, hc]

/-- For primitive even nonprincipal GRH data, the shifted polynomial criterion
produces a non-one prime through `y^2`. Pass to the primitive character, preserve
evenness at `-1`, and use conductor monotonicity of the even endpoint limit. -/
theorem exists_prime_ne_one_of_shifted_even_endpoint_polynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (heven : χ.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 8 ≤ y)
    (hpoly : 0 < fullEndpointPolynomial (Real.log q - 9 / 8) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ χ p ≠ 1 := by
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ : χ.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)⟩
  have hx : 1 < y ^ 2 := by nlinarith only [hy]
  have hY : 64 ≤ y ^ 2 := by nlinarith only [hy]
  have hlim := fullEndpointEvenLimit_neg_of_shifted_rational_polynomial_pos q hy hpoly
  have hm :=
    reciprocalGapFullEndpointEvenLimit_mono_level (le_of_lt hx) hY
      (Nat.pos_of_ne_zero χ.conductor_ne_zero) (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_of_reciprocalGapFullEndpointEvenLimit_neg hq hGRH
      χ.primitiveCharacter_isPrimitive hψ (inv_ne_one.mpr hψ)
      (reciprocalGap_primitiveCharacter_even heven) hx hY le_rfl (hm.trans_lt hlim)
  refine ⟨p, hp, hb, ?_⟩
  intro hone
  exact hv (primitiveCharacter_apply_one_of_apply_one χ hone)

end PseudoPrime.LLS.PaperStatements
