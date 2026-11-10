/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028VariationSigns
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleUnitPrincipal

/-! # Sign of the centered principal kernel beyond one -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The upper sign-change point of the principal second density lies below
one. The explicit algebraic bound on the square root controls its exponent. -/
theorem quarter_variation_upper_le_one : target028VariationUpper ≤ 1 := by
  have hs : Real.sqrt 5 ≤ (9 / 4 : ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  dsimp only [target028VariationUpper]
  apply Real.exp_le_one_iff.mpr
  linarith only [hs]

/-- The principal second density is nonnegative from one to the end of its
support. The existing sign partition then controls the combined Abel tail. -/
theorem quarter_density_nonneg_above_one {u : ℝ} (hu : 1 ≤ u) (hs : u ≤ Real.exp (21 / 8 : ℝ)) :
    0 ≤ refinedSecondDensity u := by
  apply target028_density_upper (quarter_variation_upper_le_one.trans hu)
  exact (Real.log_le_log (by linarith only [hu]) hs).trans_eq (Real.log_exp _)

/-- The signed second-density integral from one to the support endpoint is
minus the unit weight derivative. The logarithmic slope vanishes at the end
of the support, and the fundamental theorem evaluates the integral. -/
theorem quarter_density_tail_integral :
    (∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), refinedSecondDensity u) =
      -refinedWeightDeriv 1 := by
  have he : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have hI :
    IntervalIntegrable refinedSecondDensity MeasureTheory.volume 1 (Real.exp (21 / 8 : ℝ)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le he).mpr
    exact refined_second_integrable.mono_set (Set.Ioc_subset_Ioc (by norm_num only) le_rfl)
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ t * refinedWeightDeriv t)
      (by
        intro u hu
        rw [Set.uIcc_of_le he] at hu
        exact refinedWeight_log_deriv (zero_lt_one.trans_le hu.1))
      hI
  have hz : refinedWeightDeriv (Real.exp (21 / 8 : ℝ)) = 0 := by
    dsimp only [refinedWeightDeriv, refinedCoord]
    rw [Real.log_exp]
    norm_num only [mul_zero]
  rw [hz] at h
  simpa only [mul_zero, one_mul, zero_sub] using h

/-- The square-root-weighted second density has an explicit primitive on
positive arguments. Evaluating it from one to the support endpoint gives
the positive tail contribution used in the combined variation estimate. -/
theorem quarter_sqrt_density_tail_integral :
    (∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * refinedSecondDensity u) =
      target028SqrtPrimitive (Real.exp (21 / 8 : ℝ)) - target028SqrtPrimitive 1 := by
  have he : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have hi :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset refined_second_integrable
      Real.continuous_sqrt.continuousOn measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) (Real.exp (21 / 8 : ℝ)) ⊆ _)
  have hi' :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u)
      (Set.Ioc 0 (Real.exp (21 / 8 : ℝ))) := by
    simpa only [mul_comm] using hi
  have hI :
    IntervalIntegrable (fun u : ℝ ↦ Real.sqrt u * refinedSecondDensity u) MeasureTheory.volume 1
      (Real.exp (21 / 8 : ℝ)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le he).mpr
    exact hi'.mono_set (Set.Ioc_subset_Ioc (by norm_num only) le_rfl)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hI
  intro u hu
  rw [Set.uIcc_of_le he] at hu
  exact target028_sqrt_primitive_deriv (zero_lt_one.trans_le hu.1)

/-- The positive square-root-weighted density tail exceeds `179/1000`.
The explicit primitive and a certified exponential upper bound reduce the
comparison to rational arithmetic. -/
theorem quarter_sqrt_density_tail_lower :
    (179 / 1000 : ℝ) ≤
      ∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * refinedSecondDensity u := by
  rw [quarter_sqrt_density_tail_integral]
  have he := refined_exp_neg_unit_le
  dsimp only [target028SqrtPrimitive, refinedCoord]
  rw [Real.log_exp, Real.log_one]
  norm_num only [Real.exp_zero, one_mul] at he ⊢
  nlinarith only [he]

/-- On the interval from one to the support endpoint, absolute values do
not change the density integral. The density is nonnegative there. -/
theorem quarter_abs_density_tail :
    (∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), |refinedSecondDensity u|) =
      -refinedWeightDeriv 1 := by
  rw [← quarter_density_tail_integral]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u hu
  have he : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  rw [Set.uIoc_of_le he] at hu
  exact abs_of_nonneg (quarter_density_nonneg_above_one hu.1.le hu.2)

/-- The square-root-weighted absolute density tail exceeds `179/1000`.
Nonnegativity on this interval identifies it with the signed tail. -/
theorem quarter_sqrt_abs_density_tail_lower :
    (179 / 1000 : ℝ) ≤
      ∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), Real.sqrt u * |refinedSecondDensity u| := by
  apply quarter_sqrt_density_tail_lower.trans_eq
  symm
  apply intervalIntegral.integral_congr_ae
  filter_upwards with u hu
  have he : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  rw [Set.uIoc_of_le he] at hu
  rw [abs_of_nonneg (quarter_density_nonneg_above_one hu.1.le hu.2)]

/-- A full-support interval integral splits at one. The integrability
assumption is inherited by both pieces, so no endpoint contribution is lost. -/
theorem quarter_integral_split_one (f : ℝ → ℝ)
    (hf : IntervalIntegrable f MeasureTheory.volume 0 (Real.exp (21 / 8 : ℝ))) :
    (∫ u : ℝ in (0 : ℝ)..1, f u) + (∫ u : ℝ in (1 : ℝ)..Real.exp (21 / 8 : ℝ), f u) =
      ∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8 : ℝ), f u := by
  have he : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have h0 : (0 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := (Real.exp_pos _).le
  have h01 : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    apply hf.mono_set
    rw [Set.uIcc_of_le h0, Set.uIcc_of_le (by norm_num only : (0 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl he
  have h1e : IntervalIntegrable f MeasureTheory.volume 1 (Real.exp (21 / 8 : ℝ)) := by
    apply hf.mono_set
    rw [Set.uIcc_of_le h0, Set.uIcc_of_le he]
    exact Set.Icc_subset_Icc (by norm_num only) le_rfl
  exact intervalIntegral.integral_add_adjacent_intervals h01 h1e

end PseudoPrime.PrimeTestBounds.MillerRabin
