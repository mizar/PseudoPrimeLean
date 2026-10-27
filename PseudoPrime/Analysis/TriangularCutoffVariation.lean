/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # Alpha-18 cutoff variation

Explicit derivative and weighted variation estimates for Abel summation.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The positive half-line majorant is integrable; polynomial exponential moments suffice. -/
theorem triangular18_cutoff_variation_profile_integrable :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ (17 + v / 2) * Real.exp (-((1 / 4) * v)))
      (Set.Ioi 0) := by
  have h0 :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 1) (b := 1 / 4) (by norm_num only)
      (by norm_num only) (by norm_num only)
  simp only [Real.rpow_zero, Real.rpow_one, one_mul, neg_mul] at h0
  have h1 :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1 / 4) (by norm_num only)
      (by norm_num only) (by norm_num only)
  simp only [Real.rpow_one, neg_mul] at h1
  exact
    ((h0.const_mul 17).add (h1.const_mul (1 / 2))).congr
      (Filter.Eventually.of_forall
        (fun v ↦ by
          dsimp only [Pi.add_apply]; ring))

/-- The majorant integral equals 76, by the zeroth and first exponential moments. -/
theorem triangular18_cutoff_variation_profile_integral :
    (∫ v : ℝ in Set.Ioi 0, (17 + v / 2) * Real.exp (-((1 / 4) * v))) = 76 := by
  have h0 :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 1) (b := 1 / 4) (by norm_num only)
      (by norm_num only) (by norm_num only)
  simp only [Real.rpow_zero, Real.rpow_one, one_mul, neg_mul] at h0
  have h1 :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := 1 / 4) (by norm_num only)
      (by norm_num only) (by norm_num only)
  simp only [Real.rpow_one, neg_mul] at h1
  have hΓ : Real.Gamma 2 = 1 := by
    have h := Real.Gamma_nat_eq_factorial 1
    norm_num only at h
    exact h
  have hI0 :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1 / 4) (by norm_num only)
      (by norm_num only)
  norm_num only [Real.rpow_zero, Real.rpow_one, one_mul, Real.Gamma_one] at hI0
  have hI1 :=
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 / 4) (by norm_num only)
      (by norm_num only)
  norm_num only [Real.rpow_one, Real.rpow_two, hΓ] at hI1
  have he :
    (fun v : ℝ ↦ (17 + v / 2) * Real.exp (-((1 / 4) * v))) =
      (fun v : ℝ ↦ 17 * Real.exp (-((1 / 4) * v)) + (1 / 2) * (v * Real.exp (-((1 / 4) * v)))) := by
    funext v; ring
  rw [he, MeasureTheory.integral_add (h0.const_mul 17) (h1.const_mul (1 / 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hI0, hI1]
  norm_num only

/-- The absolute logarithmic variation integral is at most 76, by the integrable majorant. -/
theorem triangular18_cutoff_variation_integral_le :
    (∫ v : ℝ in Set.Ioi 0, |v / 2 - 17| * Real.exp (-((1 / 4) * v))) ≤ 76 := by
  have hb :
    ∀ᵐ v : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi 0),
      |v / 2 - 17| * Real.exp (-((1 / 4) * v)) ≤ (17 + v / 2) * Real.exp (-((1 / 4) * v)) :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
      (fun v hv ↦ by
        have hv0 : (0 : ℝ) < v := hv
        have ha : |v / 2 - 17| ≤ 17 + v / 2 :=
          abs_le.mpr ⟨by linarith only [hv0], by linarith only [hv0]⟩
        exact mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le)
  have h :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun v : ℝ ↦ mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
      triangular18_cutoff_variation_profile_integrable hb
  rw [triangular18_cutoff_variation_profile_integral] at h
  exact h

/-- For positive input the untruncated cutoff weight has the displayed derivative.
Used in Abel summation. -/
theorem triangular18_cutoff_weight_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℝ ↦ (36 + Real.log z) * z ^ (-1 / 2 : ℝ))
      (u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2)) u := by
  have hD :=
    ((Real.hasDerivAt_log hu.ne').const_add 36).mul
      (Real.hasDerivAt_rpow_const (p := -1 / 2) (Or.inl hu.ne'))
  have hp := Real.rpow_add hu (-1) (-1 / 2)
  norm_num only at hp
  rw [Real.rpow_neg_one] at hp
  apply hD.congr_deriv
  norm_num only
  rw [← hp]
  ring

/-- The logarithmic substitution gives the absolute variation profile, including its Jacobian. -/
theorem triangular18_cutoff_log_jacobian (v : ℝ) :
    |(Real.exp (-v)) ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log (Real.exp (-v))) / 2)| *
        (Real.exp (-v)) ^ (3 / 4 : ℝ) *
        Real.exp (-v) =
      |v / 2 - 17| * Real.exp (-((1 / 4) * v)) := by
  have hs :
    (Real.exp (-v)) ^ (-3 / 2 : ℝ) * (Real.exp (-v)) ^ (3 / 4 : ℝ) * Real.exp (-v) =
      Real.exp (-((1 / 4) * v)) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _), Real.log_exp,
    show (1 - (36 + -v) / 2 : ℝ) = v / 2 - 17 by ring]
  calc
    _ =
        |v / 2 - 17| *
          ((Real.exp (-v)) ^ (-3 / 2 : ℝ) * (Real.exp (-v)) ^ (3 / 4 : ℝ) * Real.exp (-v)) :=
      by ring
    _ = _ := by rw [hs]

/-- The cutoff weight vanishes at the lower endpoint, eliminating its Abel boundary term. -/
theorem triangular18_cutoff_lower_endpoint :
    (36 + Real.log (Real.exp (-36))) * Real.exp (-36) ^ (-1 / 2 : ℝ) = 0 := by
  rw [Real.log_exp]
  norm_num only [zero_mul]

/-- The logarithmic variation and upper endpoint give the explicit error budget 1456. -/
theorem triangular18_cutoff_error_budget :
    (13 : ℝ) * (36 + (∫ v : ℝ in Set.Ioi 0, |v / 2 - 17| * Real.exp (-((1 / 4) * v)))) ≤ 1456 := by
  have h := triangular18_cutoff_variation_integral_le
  linarith only [h]

/-- The weighted variation in the original variable is at most 76, by exponential substitution. -/
theorem triangular18_cutoff_original_variation_le :
    (∫ u in Real.exp (-36)..(1 : ℝ),
        |u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2)| * u ^ (3 / 4 : ℝ)) ≤
      76 := by
  let g := fun u : ℝ ↦ |u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2)| * u ^ (3 / 4 : ℝ)
  let f := fun v : ℝ ↦ |v / 2 - 17| * Real.exp (-((1 / 4) * v))
  have hg : ContinuousOn g ((fun v : ℝ ↦ Real.exp (-v)) '' Set.uIcc (0 : ℝ) 36) := by
    intro u hu
    obtain ⟨v, _, rfl⟩ := hu
    have hp := Real.exp_pos (-v)
    have hD :
      ContinuousAt (fun u : ℝ ↦ u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2)) (Real.exp (-v)) :=
      (Real.continuousAt_rpow_const _ (-3 / 2) (Or.inl hp.ne')).mul
        (continuousAt_const.sub
          ((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const 2))
    exact (hD.abs.mul (Real.continuousAt_rpow_const _ (3 / 4) (Or.inl hp.ne'))).continuousWithinAt
  have hs :=
    intervalIntegral.integral_comp_mul_deriv' (a := (0 : ℝ)) (b := 36) (f := fun v : ℝ ↦
      Real.exp (-v)) (f' := fun v : ℝ ↦ -Real.exp (-v)) (g := g)
      (fun v _ ↦ by simpa only [Pi.neg_apply, id_eq, mul_neg_one] using (hasDerivAt_id v).neg.exp)
      ((Real.continuous_exp.comp continuous_id.neg).neg.continuousOn) hg
  have he (v : ℝ) : g (Real.exp (-v)) * (-Real.exp (-v)) = -f v := by
    dsimp only [g, f]
    rw [mul_neg, triangular18_cutoff_log_jacobian]
  have hleft :
    (∫ v in (0 : ℝ)..36, (g ∘ (fun v : ℝ ↦ Real.exp (-v))) v * (-Real.exp (-v))) =
      -(∫ v in (0 : ℝ)..36, f v) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun v _ ↦ he v)
  have hrev : (∫ u in (1 : ℝ)..Real.exp (-36), g u) = -(∫ u in Real.exp (-36)..(1 : ℝ), g u) :=
    intervalIntegral.integral_symm _ _
  rw [hleft, neg_zero, Real.exp_zero, hrev] at hs
  have hEq := (neg_injective hs).symm
  have hi : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    have hc : Continuous f :=
      ((continuous_id.div_const 2).sub continuous_const).abs.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg)
    apply triangular18_cutoff_variation_profile_integrable.mono' hc.aestronglyMeasurable
    apply (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
    intro v hv
    have hv0 : (0 : ℝ) < v := hv
    have ha : |v / 2 - 17| ≤ 17 + v / 2 :=
      abs_le.mpr ⟨by linarith only [hv0], by linarith only [hv0]⟩
    change ‖|v / 2 - 17| * Real.exp (-((1 / 4) * v))‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le
  have hb :=
    MeasureTheory.setIntegral_mono_set hi
      (Filter.Eventually.of_forall
        (fun v : ℝ ↦ mul_nonneg (abs_nonneg (v / 2 - 17)) (Real.exp_pos _).le))
      (Filter.Eventually.of_forall (fun v (hv : v ∈ Set.Ioc (0 : ℝ) 36) ↦ hv.1))
  change (∫ u in Real.exp (-36)..(1 : ℝ), g u) ≤ _
  rw [hEq, intervalIntegral.integral_of_le (by norm_num only : (0 : ℝ) ≤ 36)]
  exact hb.trans triangular18_cutoff_variation_integral_le

/-- The upper endpoint and weighted variation together give budget 1456
for a Chebyshev error constant 13. -/
theorem triangular18_cutoff_endpoint_variation_budget :
    (13 : ℝ) *
        (|(36 + Real.log 1) * (1 : ℝ) ^ (-1 / 2 : ℝ)| +
          (∫ u in Real.exp (-36)..(1 : ℝ),
            |u ^ (-3 / 2 : ℝ) * (1 - (36 + Real.log u) / 2)| * u ^ (3 / 4 : ℝ))) ≤
      1456 := by
  norm_num only [Real.log_one, Real.one_rpow]
  have h := triangular18_cutoff_original_variation_le
  linarith only [h]

end PseudoPrime.Analysis
