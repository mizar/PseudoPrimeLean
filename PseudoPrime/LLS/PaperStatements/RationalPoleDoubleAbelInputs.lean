/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPolePrincipalWeight
public import PseudoPrime.LLS.RiemannWeightedErrorGlobal

/-!
# Inputs for double Abel summation with the selected fourth-pole kernel

The density and endpoint bounds concern the fixed LLS kernel. Keeping these evaluations
in a separate module prevents changes to the selected profile from rebuilding unrelated
principal estimates. The global Mangoldt bound supplies the arithmetic error at every
nonnegative argument, including arguments below the first positive integer.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The cubic Taylor lower bound for exp(14/13) gives the reciprocal rational cap.
All four Taylor coefficients are evaluated exactly; positivity justifies inversion.
This fixed-profile coefficient controls both unit-cutoff boundary errors. -/
private theorem exp_fourPoleCoord_neg_le : Real.exp (-(14 / 13 : ℝ)) ≤ (6591 / 18883 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14 / 13) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    pow_zero, pow_one] at h
  rw [Real.exp_neg]
  have hi := (inv_le_inv₀ (Real.exp_pos _) (by norm_num only : (0 : ℝ) < 18883 / 6591)).mpr h
  norm_num only at hi
  exact hi

/-- The selected principal weight at the unit cutoff is strictly below one thirteenth.
Evaluate its logarithmic coordinate and apply the reciprocal cubic Taylor certificate.
This preserves the small coefficient of the hard-cutoff Chebyshev error. -/
theorem fourPoleWeight_one_lt : fourPoleWeight 1 < (1 / 13 : ℝ) := by
  have he := exp_fourPoleCoord_neg_le
  norm_num only [fourPoleWeight, fourPoleCoord, Real.log_one, mul_zero, sub_zero, Real.sqrt_one,
    mul_one]
  nlinarith only [he]

/-- The absolute derivative at the unit cutoff is strictly below one fifth.
Evaluate the explicit derivative and use the same rational exponential certificate.
This bounds the logarithmically weighted boundary error in double Abel summation. -/
theorem fourPoleWeightDeriv_one_lt : |fourPoleWeightDeriv 1| < (1 / 5 : ℝ) := by
  have he := exp_fourPoleCoord_neg_le
  norm_num only [fourPoleWeightDeriv, fourPoleCoord, Real.log_one, mul_zero, sub_zero,
    Real.sqrt_one, mul_one]
  rw [abs_mul, abs_div, abs_of_pos (Real.exp_pos _)]
  norm_num only
  nlinarith only [he]

/-- The explicit second Abel density for the fixed fourth-pole principal weight.
For positive u it is the derivative of u times the first weight derivative.
The signed cubic polynomial is later bounded by three positive logarithmic moments. -/
noncomputable def fourPoleSecondDensity (u : ℝ) : ℝ :=
  Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
    ((6 / 13 : ℝ) ^ 2 * fourPoleCoord u ^ 3 -
        6 * (25 / 26 : ℝ) * (6 / 13 : ℝ) * fourPoleCoord u ^ 2 +
      6 * (25 / 26 : ℝ) ^ 2 * fourPoleCoord u)

/-- At every positive argument, differentiating u*w'(u) gives the second Abel density.
Apply the coordinate, exponential, square-root and polynomial derivative rules;
explicit denominator nonzeroness and the square-root square identity normalize the result.
This connects the actual K4 weight to the logarithmic reconstruction formula. -/
theorem fourPoleWeight_log_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t ↦ t * fourPoleWeightDeriv t) (fourPoleSecondDensity u) u := by
  have hv := fourPoleCoord_hasDerivAt hu
  have hs := (Real.sqrt_pos.mpr hu).ne'
  have hd := ((hasDerivAt_id u).const_mul 6).mul (Real.hasDerivAt_sqrt hu.ne')
  have hp := ((hv.pow 3).const_mul (6 / 13 : ℝ)).sub ((hv.pow 2).const_mul (75 / 26 : ℝ))
  have h :=
    (hasDerivAt_id u).mul
      ((hv.neg.exp.div hd (mul_ne_zero (mul_ne_zero (by norm_num only) hu.ne') hs)).mul hp)
  apply h.congr_deriv
  dsimp only [fourPoleSecondDensity, Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply,
    Pi.neg_apply, id_eq]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  field_simp (disch :=
    first
    | exact hu.ne'
    | exact hs
    | norm_num only)
  rw [Real.sq_sqrt hu.le]
  ring

end PseudoPrime.LLS.PaperStatements
