/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleCutoff
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual fourth-order principal weight and explicit unit-cutoff weighted variation. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The logarithmic coordinate v(u)=14/13-(25/26)log u of the fourth-order profile.
For positive u this is the inverse-transform coordinate; it is nonnegative on the support.
It is used in the concrete weight, derivative and moment bounds below. -/
noncomputable def fourPoleCoord (u : ℝ) : ℝ :=
  14 / 13 - (25 / 26) * Real.log u

/-- The uncut algebraic principal weight v(u)^3 exp(-v(u))/(6 sqrt u).
On the positive support it equals the actual kernel transform divided by sqrt u.
Outside that support this formula is only an auxiliary expression. It permits direct
differentiation and logarithmic-moment evaluation without changing the actual kernel. -/
noncomputable def fourPoleWeight (u : ℝ) : ℝ :=
  fourPoleCoord u ^ 3 * Real.exp (-fourPoleCoord u) / (6 * Real.sqrt u)

/-- The explicit derivative of the uncut principal weight at positive u.
It is exp(-v)/(6u sqrt u) times ((6/13)v^3-(75/26)v^2).
The factored form supplies the absolute derivative majorant for quantitative Abel estimates. -/
noncomputable def fourPoleWeightDeriv (u : ℝ) : ℝ :=
  Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
    ((6 / 13 : ℝ) * fourPoleCoord u ^ 3 - (75 / 26 : ℝ) * fourPoleCoord u ^ 2)

/-- The logarithmic coordinate has derivative -(25/26)/u for positive u.
Differentiate the real logarithm and normalize the coefficient.
This is the chain-rule input for the principal weight. -/
theorem fourPoleCoord_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt fourPoleCoord (-(25 / 26 : ℝ) / u) u := by
  have h :=
    (hasDerivAt_const u (14 / 13 : ℝ)).sub ((Real.hasDerivAt_log hu.ne').const_mul (25 / 26 : ℝ))
  convert h using 1
  · rfl
  · ring

/-- For positive u and arbitrary real v and E, normalize the quotient-rule expression
for the selected fourth-order weight. Explicit inverse cancellations and sqrt(u)^2=u
prove the algebraic identity used by its derivative theorem. -/
private theorem fourPole_deriv_algebra {u : ℝ} (hu : 0 < u) (v E : ℝ) :
    E / (6 * u * Real.sqrt u) * (6 / 13 * v ^ 3 - 75 / 26 * v ^ 2) =
      ((3 * v ^ 2 * (-(25 / 26) / u) * E + v ^ 3 * (E * -(-(25 / 26) / u))) * (6 * Real.sqrt u) -
          v ^ 3 * E * (6 * (1 / (2 * Real.sqrt u)))) /
        (6 * Real.sqrt u) ^ 2 := by
  apply (mul_left_injective₀ (mul_ne_zero hu.ne' (pow_ne_zero 3 (Real.sqrt_pos.mpr hu).ne')))
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf
  simp only [show Real.sqrt u ^ 3 = Real.sqrt u * Real.sqrt u * Real.sqrt u by ring,
    show Real.sqrt u ^ 4 = Real.sqrt u * Real.sqrt u * Real.sqrt u * Real.sqrt u by ring,
    show (Real.sqrt u)⁻¹ ^ 3 = (Real.sqrt u)⁻¹ * (Real.sqrt u)⁻¹ * (Real.sqrt u)⁻¹ by ring, pow_two,
    mul_assoc, mul_inv_cancel_left₀ hu.ne', mul_inv_cancel_left₀ (Real.sqrt_pos.mpr hu).ne']
  ring_nf
  simp only [Real.sq_sqrt hu.le]
  ring

/-- At every positive u, the uncut weight has the explicit factored derivative.
Use the polynomial, exponential and square-root quotient rules, then sqrt(u)^2=u.
This supplies a derivative formula without an unspecified analytic error. -/
theorem fourPoleWeight_hasDerivAt {u : ℝ} (hu : 0 < u) :
    HasDerivAt fourPoleWeight (fourPoleWeightDeriv u) u := by
  have hv := fourPoleCoord_hasDerivAt hu
  have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have h :=
    ((hv.pow 3).mul hv.neg.exp).div ((Real.hasDerivAt_sqrt hu.ne').const_mul 6)
      (mul_ne_zero (by norm_num only) hs)
  convert h using 1
  · rfl
  · change
      fourPoleWeightDeriv u =
        ((3 * fourPoleCoord u ^ 2 * (-(25 / 26 : ℝ) / u) * Real.exp (-fourPoleCoord u) +
                fourPoleCoord u ^ 3 * (Real.exp (-fourPoleCoord u) * -(-(25 / 26 : ℝ) / u))) *
              (6 * Real.sqrt u) -
            fourPoleCoord u ^ 3 * Real.exp (-fourPoleCoord u) * (6 * (1 / (2 * Real.sqrt u)))) /
          (6 * Real.sqrt u) ^ 2
    dsimp only [fourPoleWeightDeriv]
    exact fourPole_deriv_algebra hu (fourPoleCoord u) (Real.exp (-fourPoleCoord u))

/-- On the positive support log u<=28/25, the actual principal weight equals
the uncut algebraic expression. Apply the proved inverse transform and normalize v(u).
This connects the elementary formula to the original admissible kernel. -/
theorem fourPoleKernelWeight_eq {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 28 / 25) :
    (rationalPoleFourKernel.transform u).re / Real.sqrt u = fourPoleWeight u := by
  rw [rationalPoleFourKernel,
    rationalPole_transform (m := 2) (a := 13 / 25) (c := 14 / 25) (u := u) (by norm_num only)
      (by norm_num only) (by norm_num only) hu,
    Complex.ofReal_re, Analysis.rationalPoleProfile]
  have ha : 0 < u ∧ Real.log u ≤ 2 * (14 / 25 : ℝ) := ⟨hu, by linarith only [hl]⟩
  rw [ite_eq_left ha]
  have he : (2 * (14 / 25 : ℝ) - Real.log u) / (2 * (13 / 25 : ℝ)) = fourPoleCoord u := by
    dsimp only [fourPoleCoord]
    ring
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.factorial, Nat.cast_ofNat]
  norm_num only at he
  rw [he]
  dsimp only [fourPoleWeight]
  ring

/-- The positive-support majorant for the principal weight's absolute derivative.
Replace the difference of the cubic and quadratic terms by their sum.
Its three-quarter-power weighted integral is evaluated exactly by logarithmic moments. -/
noncomputable def fourPoleVariationMajorant (u : ℝ) : ℝ :=
  Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
    ((6 / 13 : ℝ) * fourPoleCoord u ^ 3 + (75 / 26 : ℝ) * fourPoleCoord u ^ 2)

/-- On the positive support, the absolute derivative is at most its positive majorant.
Use v(u)>=0 and the triangle inequality on the cubic-minus-quadratic expression.
This pointwise bound permits integration against the explicit psi-error weight. -/
theorem fourPoleWeightDeriv_abs_le {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 28 / 25) :
    |fourPoleWeightDeriv u| ≤ fourPoleVariationMajorant u := by
  have hv : 0 ≤ fourPoleCoord u := by
    dsimp only [fourPoleCoord]
    linarith only [hl]
  have hc : 0 ≤ Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) :=
    div_nonneg (Real.exp_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hu.le) (Real.sqrt_nonneg _))
  rw [fourPoleWeightDeriv, abs_mul, abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left ?_ hc
  calc
    _ ≤ |(6 / 13 : ℝ) * fourPoleCoord u ^ 3| + |(75 / 26 : ℝ) * fourPoleCoord u ^ 2| := abs_sub _ _
    _ = _ := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6 / 13) (pow_nonneg hv 3)),
        abs_of_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 75 / 26) (sq_nonneg _))]

/-- For positive u, combine exponential modulation and the square-root denominator
with u^(3/4) into exp(-14/13)u^(11/52). Expand positive real powers into exponentials.
This reduces the weighted derivative majorant to positive logarithmic moments. -/
theorem fourPoleWeight_power_factor {u : ℝ} (hu : 0 < u) :
    u ^ (3 / 4 : ℝ) * Real.exp (-fourPoleCoord u) / (u * Real.sqrt u) =
      Real.exp (-(14 / 13 : ℝ)) * u ^ (11 / 52 : ℝ) := by
  calc
    _ =
        (Real.exp (Real.log u * (3 / 4)) * Real.exp (-fourPoleCoord u)) /
          (Real.exp (Real.log u) * Real.exp (Real.log u * (1 / 2))) :=
      by rw [Real.rpow_def_of_pos hu, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, Real.exp_log hu]
    _ = Real.exp (-(14 / 13 : ℝ)) * Real.exp (Real.log u * (11 / 52)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      dsimp only [fourPoleCoord]
      ring
    _ = _ := by rw [Real.rpow_def_of_pos hu]

/-- The weighted derivative majorant is a fixed linear combination of two log moments.
Normalize v(u)=(25/26)(28/25-log u) and use the exact power factor.
This identity exposes the quadratic and cubic terms for exact integration. -/
theorem fourPoleVariationMajorant_eq {u : ℝ} (hu : 0 < u) :
    u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u =
      (Real.exp (-(14 / 13 : ℝ)) / 6) *
        ((6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 3 * (u ^ (11 / 52 : ℝ) * (28 / 25 - Real.log u) ^ 3) +
          (75 / 26 : ℝ) * (25 / 26 : ℝ) ^ 2 *
            (u ^ (11 / 52 : ℝ) * (28 / 25 - Real.log u) ^ 2)) := by
  have hv : fourPoleCoord u = (25 / 26 : ℝ) * (28 / 25 - Real.log u) := by
    dsimp only [fourPoleCoord]
    ring
  have he :
    u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u =
      (u ^ (3 / 4 : ℝ) * Real.exp (-fourPoleCoord u) / (u * Real.sqrt u)) / 6 *
        ((6 / 13 : ℝ) * fourPoleCoord u ^ 3 + (75 / 26 : ℝ) * fourPoleCoord u ^ 2) := by
    dsimp only [fourPoleVariationMajorant]
    ring
  rw [he, fourPoleWeight_power_factor hu, hv]
  ring

/-- The three-quarter-power weighted derivative majorant is integrable on (0,1].
Its integral is (27017602324/11536418439)exp(-14/13).
Use the existing shifted second and third logarithmic moments with parameter 63/52.
This supplies an exact finite variation budget without numerical quadrature. -/
theorem fourPoleVariationMajorant_integral :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u)
        (Set.Ioc 0 1) ∧
      (∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u) =
        (27017602324 / 11536418439 : ℝ) * Real.exp (-(14 / 13 : ℝ)) := by
  have h2 := Analysis.shifted_log_moment 2 (28 / 25) (s := 63 / 52) (by norm_num only)
  have h3 := Analysis.shifted_log_moment 3 (28 / 25) (s := 63 / 52) (by norm_num only)
  norm_num only at h2 h3
  have hi :=
    ((h3.1.const_mul ((6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 3)).add
          (h2.1.const_mul ((75 / 26 : ℝ) * (25 / 26 : ℝ) ^ 2))).const_mul
      (Real.exp (-(14 / 13 : ℝ)) / 6)
  have hEq :
    (fun u : ℝ ↦
        u ^ (3 / 4 : ℝ) *
          fourPoleVariationMajorant u) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 1)]
      (fun u : ℝ ↦
        (Real.exp (-(14 / 13 : ℝ)) / 6) *
          ((6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 3 * (u ^ (11 / 52 : ℝ) * (28 / 25 - Real.log u) ^ 3) +
            (75 / 26 : ℝ) * (25 / 26 : ℝ) ^ 2 *
              (u ^ (11 / 52 : ℝ) * (28 / 25 - Real.log u) ^ 2))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact fourPoleVariationMajorant_eq hu.1
  refine ⟨hi.congr hEq.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae hEq, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add (h3.1.const_mul ((6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 3))
      (h2.1.const_mul ((75 / 26 : ℝ) * (25 / 26 : ℝ) ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, h3.2, h2.2]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.choose_one_right, Nat.choose, Nat.factorial, Nat.reduceAdd, Nat.reduceSub,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

/-- The actual absolute derivative of the uncut weight has weighted integral below three
on (0,1], and is integrable there. Dominate it by the exactly integrated majorant.
Measurability and the positive-domain derivative bound justify domination.
This is the quantitative interior term for the truncated principal weight. -/
theorem fourPoleWeightDeriv_integral :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|)
        (Set.Ioc 0 1) ∧
      (∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|) < 3 := by
  have hv : Measurable fourPoleCoord :=
    measurable_const.sub (measurable_const.mul Real.measurable_log)
  have hD : Measurable fourPoleWeightDeriv :=
    ((Real.measurable_exp.comp hv.neg).div
          ((measurable_const.mul measurable_id).mul Real.continuous_sqrt.measurable)).mul
      ((measurable_const.mul (hv.pow_const 3)).sub (measurable_const.mul (hv.pow_const 2)))
  have hb :
    ∀ᵐ u ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
      u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u| ≤
        u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact
      mul_le_mul_of_nonneg_left
        (fourPoleWeightDeriv_abs_le hu.1 ((Real.log_nonpos hu.1.le hu.2).trans (by norm_num only)))
        (Real.rpow_nonneg hu.1.le _)
  have hI :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|)
      (Set.Ioc 0 1) := by
    apply
      fourPoleVariationMajorant_integral.1.mono'
        ((measurable_id.pow_const (3 / 4 : ℝ)).mul
            (continuous_abs.measurable.comp hD)).aestronglyMeasurable
    filter_upwards [hb, MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu hmem
    dsimp only [Pi.mul_apply, id_eq, Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hmem.1.le _) (abs_nonneg _))]
    exact hu
  refine ⟨hI, ?_⟩
  have hi := MeasureTheory.integral_mono_ae hI fourPoleVariationMajorant_integral.1 hb
  rw [fourPoleVariationMajorant_integral.2] at hi
  apply hi.trans_lt
  have he : Real.exp (-(14 / 13 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  calc
    _ ≤ (27017602324 / 11536418439 : ℝ) * 1 := mul_le_mul_of_nonneg_left he (by norm_num only)
    _ < 3 := by norm_num only

/-- The uncut principal weight at one lies between zero and one.
Evaluate v(1), bound its negative exponential by one and compare rational coefficients.
This supplies the boundary term in the weighted variation budget. -/
theorem fourPoleWeight_endpoint : 0 ≤ fourPoleWeight 1 ∧ fourPoleWeight 1 ≤ 1 := by
  have he : Real.exp (-(14 / 13 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num only)
  have hn : fourPoleWeight 1 = ((14 / 13 : ℝ) ^ 3 / 6) * Real.exp (-(14 / 13 : ℝ)) := by
    norm_num only [fourPoleWeight, fourPoleCoord, Real.log_one, mul_zero, sub_zero, Real.sqrt_one,
      mul_one]
    ring
  rw [hn]
  constructor
  · exact mul_nonneg (by norm_num only) (Real.exp_nonneg _)
  · exact (mul_le_mul_of_nonneg_left he (by norm_num only)).trans (by norm_num only)

/-- The endpoint term plus the three-quarter-power weighted absolute derivative integral
of the uncut weight is below four. Combine the endpoint and integral estimates.
This is the explicit variation constant entering a quantitative Abel comparison. -/
theorem fourPoleWeight_variation_lt_four :
    1 ^ (3 / 4 : ℝ) * |fourPoleWeight 1| +
        (∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|) <
      4 := by
  rw [Real.one_rpow, one_mul, abs_of_nonneg fourPoleWeight_endpoint.1]
  linarith only [fourPoleWeight_endpoint.2, fourPoleWeightDeriv_integral.2]

/-- The actual fourth-order inverse transform divided by sqrt u.
This is the scaled principal-character weight in weighted Mangoldt sums.
Unlike the uncut algebraic expression it retains the actual compact-support convention.
Its interior derivative and weighted variation are certified below. -/
noncomputable def fourPoleKernelWeight (u : ℝ) : ℝ :=
  (rationalPoleFourKernel.transform u).re / Real.sqrt u

/-- At positive u strictly inside the support, the actual kernel weight has the
explicit algebraic derivative. The support inequalities persist in a neighborhood,
where the actual weight equals the uncut formula. Transfer its derivative locally.
This connects the formula to derivative-based weighted-sum estimates. -/
theorem fourPoleKernelWeight_hasDerivAt {u : ℝ} (hu : 0 < u) (hl : Real.log u < 28 / 25) :
    HasDerivAt fourPoleKernelWeight (fourPoleWeightDeriv u) u := by
  have hlog : ∀ᶠ v : ℝ in nhds u, Real.log v < 28 / 25 :=
    Filter.Tendsto.eventually_lt_const hl (Real.continuousAt_log hu.ne')
  have he : fourPoleKernelWeight =ᶠ[nhds u] fourPoleWeight := by
    filter_upwards [eventually_gt_nhds hu, hlog] with v hv hvl
    exact fourPoleKernelWeight_eq hv hvl.le
  exact (fourPoleWeight_hasDerivAt hu).congr_of_eventuallyEq he

/-- The actual kernel weight has integrable three-quarter-power weighted absolute
derivative on (0,1], with integral below three. Identify its derivative at every
point of the interval, then transfer the proved auxiliary integral bound.
No arithmetic estimate or RH assumption enters this analytic statement. -/
theorem fourPoleKernelWeight_deriv_integral :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u|)
        (Set.Ioc 0 1) ∧
      (∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u|) < 3 := by
  have he :
    (fun u : ℝ ↦
        u ^ (3 / 4 : ℝ) *
          |deriv fourPoleKernelWeight u|) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 1)]
      (fun u : ℝ ↦ u ^ (3 / 4 : ℝ) * |fourPoleWeightDeriv u|) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    rw [(fourPoleKernelWeight_hasDerivAt hu.1
          ((Real.log_nonpos hu.1.le hu.2).trans_lt (by norm_num only))).deriv]
  refine ⟨fourPoleWeightDeriv_integral.1.congr he.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae he]
  exact fourPoleWeightDeriv_integral.2

/-- The actual kernel weight has total unit-cutoff weighted variation below four.
Transfer the endpoint formula and use the derivative bound for the actual transform.
This gives the concrete analytic input for a psi-based truncated principal comparison;
the weighted Mangoldt error theorem itself is not asserted here. -/
theorem fourPoleKernelWeight_variation_lt_four :
    |fourPoleKernelWeight 1| +
        (∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u|) <
      4 := by
  have he : fourPoleKernelWeight 1 = fourPoleWeight 1 :=
    fourPoleKernelWeight_eq (by norm_num only) (by norm_num only [Real.log_one])
  rw [he, abs_of_nonneg fourPoleWeight_endpoint.1]
  linarith only [fourPoleWeight_endpoint.2, fourPoleKernelWeight_deriv_integral.2]

/-- The actual unit-cutoff kernel weight has weighted absolute derivative integral below one.
Use the exact majorant moment and exp(-14/13)<=169/400,
obtained by squaring exp(7/13)>=20/13.
This sharpens the coarse variation budget using only a fixed rational comparison. -/
theorem fourPoleKernelWeight_integral_lt_one :
    (∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u|) < 1 := by
  have he : Real.exp (-(14 / 13 : ℝ)) ≤ 169 / 400 := by
    have h := Real.add_one_le_exp (7 / 13 : ℝ)
    have hp : (400 / 169 : ℝ) ≤ Real.exp (14 / 13) := by
      rw [show (14 / 13 : ℝ) = 7 / 13 + 7 / 13 by norm_num only, Real.exp_add]
      nlinarith only [h, Real.exp_pos (7 / 13 : ℝ)]
    rw [Real.exp_neg, ← one_div]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by nlinarith only [hp])
  have hb :
    ∀ᵐ u ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
      u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u| ≤
        u ^ (3 / 4 : ℝ) * fourPoleVariationMajorant u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    rw [(fourPoleKernelWeight_hasDerivAt hu.1
          ((Real.log_nonpos hu.1.le hu.2).trans_lt (by norm_num only))).deriv]
    exact
      mul_le_mul_of_nonneg_left
        (fourPoleWeightDeriv_abs_le hu.1 ((Real.log_nonpos hu.1.le hu.2).trans (by norm_num only)))
        (Real.rpow_nonneg hu.1.le _)
  have hi :=
    MeasureTheory.integral_mono_ae fourPoleKernelWeight_deriv_integral.1
      fourPoleVariationMajorant_integral.1 hb
  rw [fourPoleVariationMajorant_integral.2] at hi
  apply hi.trans_lt
  calc
    _ ≤ (27017602324 / 11536418439 : ℝ) * (169 / 400) :=
      mul_le_mul_of_nonneg_left he (by norm_num only)
    _ < 1 := by norm_num only

/-- The actual unit-cutoff kernel weight has endpoint plus weighted variation below two.
Combine the actual derivative integral below one with the endpoint bound at one.
This is a concrete analytic constant for the truncated principal Abel comparison. -/
theorem fourPoleKernelWeight_variation_lt_two :
    |fourPoleKernelWeight 1| +
        (∫ u : ℝ in Set.Ioc 0 1, u ^ (3 / 4 : ℝ) * |deriv fourPoleKernelWeight u|) <
      2 := by
  have he : fourPoleKernelWeight 1 = fourPoleWeight 1 :=
    fourPoleKernelWeight_eq (by norm_num only) (by norm_num only [Real.log_one])
  rw [he, abs_of_nonneg fourPoleWeight_endpoint.1]
  linarith only [fourPoleWeight_endpoint.2, fourPoleKernelWeight_integral_lt_one]

end PseudoPrime.LLS.PaperStatements
