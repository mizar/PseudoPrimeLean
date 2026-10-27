/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularCutoffVariation

/-! # Exact upper-support alpha-18 main and variation integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- At positive input, the upper triangular weight has the displayed derivative.
Differentiate the logarithmic factor and real power; used in finite Abel summation. -/
theorem triangular18_upper_weight_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℝ ↦ (36 - Real.log z) * z ^ (-1 / 2 : ℝ))
      (u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19)) u := by
  have hD :=
    ((Real.hasDerivAt_log hu.ne').const_sub 36).mul
      (Real.hasDerivAt_rpow_const (p := -1 / 2) (Or.inl hu.ne'))
  have hp := Real.rpow_add hu (-1) (-1 / 2)
  norm_num only at hp
  rw [Real.rpow_neg_one] at hp
  apply hD.congr_deriv
  norm_num only
  rw [neg_mul, ← hp]
  ring

/-- At positive input, an explicit primitive differentiates to the upper
Abel main integrand. Power addition reduces the exponent factors. -/
theorem triangular18_upper_main_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℝ ↦ z ^ (1 / 2 : ℝ) * (Real.log z - 40))
      (u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19) * u) u := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := 1 / 2) (Or.inl hu.ne')).mul
      ((Real.hasDerivAt_log hu.ne').sub_const 40)
  have hp : u ^ (1 / 2 : ℝ) = u ^ (-1 / 2 : ℝ) * u := by
    have e := Real.rpow_add hu (-1 / 2) 1
    norm_num only [Real.rpow_one] at e
    simpa only [neg_div] using e
  have hm : u ^ (-1 / 2 : ℝ) = u ^ (-3 / 2 : ℝ) * u := by
    have e := Real.rpow_add hu (-3 / 2) 1
    norm_num only [Real.rpow_one] at e
    simpa only [neg_div] using e
  apply h.congr_deriv
  norm_num only
  rw [hp]
  field_simp [hu.ne']
  simp only [neg_div] at hm
  rw [hm]
  ring

/-- The upper Abel main integral from one to exp 36 equals 40 minus 4 exp 18.
Apply the fundamental theorem to the explicit primitive on the positive interval. -/
theorem triangular18_upper_main_integral :
    (∫ u in (1 : ℝ)..Real.exp 36, u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19) * u) =
      40 - 4 * Real.exp 18 := by
  have hab : (1 : ℝ) ≤ Real.exp 36 := Real.one_le_exp_iff.mpr (by norm_num only)
  have hc :
    ContinuousOn (fun u : ℝ ↦ u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19) * u)
      (Set.uIcc 1 (Real.exp 36)) := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    have hp : 0 < u := zero_lt_one.trans_le hu.1
    exact
      (((Real.continuousAt_rpow_const u (-3 / 2) (Or.inl hp.ne')).mul
              ((Real.continuousAt_log hp.ne').div_const 2 |>.sub continuousAt_const)).mul
          continuousAt_id).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu ↦
        triangular18_upper_main_deriv
          (by
            rw [Set.uIcc_of_le hab] at hu
            exact zero_lt_one.trans_le hu.1))
      hc.intervalIntegrable
  rw [Real.one_rpow, Real.log_one, Real.log_exp, ← Real.exp_mul] at h
  norm_num only [one_mul, zero_sub] at h
  convert h using 1
  · congr 1
    funext u
    rw [neg_div]
  · ring

/-- At positive input, the weighted upper variation has an explicit primitive.
Differentiate its logarithmic power expression to prepare the error integral. -/
theorem triangular18_upper_variation_deriv {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℝ ↦ z ^ (1 / 4 : ℝ) * (84 - 2 * Real.log z))
      (u ^ (-3 / 4 : ℝ) * (19 - Real.log u / 2)) u := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := 1 / 4) (Or.inl hu.ne')).mul
      (((Real.hasDerivAt_log hu.ne').const_mul 2).const_sub 84)
  have hp : u ^ (1 / 4 : ℝ) = u ^ (-3 / 4 : ℝ) * u := by
    have e := Real.rpow_add hu (-3 / 4) 1
    norm_num only [Real.rpow_one] at e
    simpa only [neg_div] using e
  apply h.congr_deriv
  norm_num only
  rw [hp]
  field_simp [hu.ne']
  ring

/-- On the upper support interval, the derivative has negative sign and
its weighted absolute value is the displayed nonnegative profile.
Logarithmic monotonicity controls the sign and combines the real powers. -/
theorem triangular18_upper_variation_profile {u : ℝ} (hl : 1 ≤ u) (hr : u ≤ Real.exp 36) :
    |u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19)| * u ^ (3 / 4 : ℝ) =
      u ^ (-3 / 4 : ℝ) * (19 - Real.log u / 2) := by
  have hu := zero_lt_one.trans_le hl
  have hlog := Real.log_le_log hu hr
  rw [Real.log_exp] at hlog
  have hn : Real.log u / 2 - 19 ≤ 0 := by linarith only [hlog]
  have hp := Real.rpow_add hu (-3 / 2) (3 / 4)
  norm_num only at hp
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.le _), abs_of_nonpos hn]
  calc
    _ = (u ^ (-3 / 2 : ℝ) * u ^ (3 / 4 : ℝ)) * (19 - Real.log u / 2) := by ring
    _ = _ := by simpa only [neg_div] using congrArg (fun z : ℝ ↦ z * (19 - Real.log u / 2)) hp.symm

/-- The weighted upper derivative variation integral equals 12 exp 9 minus 84.
Replace the absolute value by its signed profile and evaluate the explicit primitive.
This is the upper-branch Chebyshev error budget for the full principal series. -/
theorem triangular18_upper_variation_integral :
    (∫ u in (1 : ℝ)..Real.exp 36, |u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19)| * u ^ (3 / 4 : ℝ)) =
      12 * Real.exp 9 - 84 := by
  have hab : (1 : ℝ) ≤ Real.exp 36 := Real.one_le_exp_iff.mpr (by norm_num only)
  have hc :
    ContinuousOn (fun u : ℝ ↦ u ^ (-3 / 4 : ℝ) * (19 - Real.log u / 2))
      (Set.uIcc 1 (Real.exp 36)) := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    have hp : 0 < u := zero_lt_one.trans_le hu.1
    exact
      ((Real.continuousAt_rpow_const u (-3 / 4) (Or.inl hp.ne')).mul
          (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu ↦
        triangular18_upper_variation_deriv
          (by
            rw [Set.uIcc_of_le hab] at hu
            exact zero_lt_one.trans_le hu.1))
      hc.intervalIntegrable
  have he :
    (∫ u in (1 : ℝ)..Real.exp 36, |u ^ (-3 / 2 : ℝ) * (Real.log u / 2 - 19)| * u ^ (3 / 4 : ℝ)) =
      ∫ u in (1 : ℝ)..Real.exp 36, u ^ (-3 / 4 : ℝ) * (19 - Real.log u / 2) :=
    intervalIntegral.integral_congr
      (fun u hu ↦ by
        rw [Set.uIcc_of_le hab] at hu
        exact triangular18_upper_variation_profile hu.1 hu.2)
  rw [he, h, Real.one_rpow, Real.log_one, Real.log_exp, ← Real.exp_mul]
  norm_num only [one_mul, mul_zero, sub_zero]
  ring

end PseudoPrime.Analysis
