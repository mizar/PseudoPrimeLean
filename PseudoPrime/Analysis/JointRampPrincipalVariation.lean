/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialAbsoluteVariation
public import PseudoPrime.Analysis.ExponentialRampPairedJumps

/-! # Density bounds after combining ramp and principal variations -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The absolute left variation mass through the ramp entrance is at most three quarters.
Split at one, evaluate the signed primitive, and use exp(-1) at most three eighths. This retains
a smaller compact-support cost in a joint ramp-principal comparison. -/
theorem ramp_left_abs_integral_le_three_quarters :
    (∫ u in (0 : ℝ)..(247 / 100), |exponentialRampVariationLeft u|) ≤ 3 / 4 := by
  have hc : Continuous exponentialRampVariationLeft :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hl :
    (∫ u in (0 : ℝ)..1, |exponentialRampVariationLeft u|) =
      -(∫ u in (0 : ℝ)..1, exponentialRampVariationLeft u) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num only : (0 : ℝ) ≤ 1)] at hu
    dsimp only
    exact abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.2) (Real.exp_pos _).le)
  have hr :
    (∫ u in (1 : ℝ)..(247 / 100), |exponentialRampVariationLeft u|) =
      ∫ u in (1 : ℝ)..(247 / 100), exponentialRampVariationLeft u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num only : (1 : ℝ) ≤ 247 / 100)] at hu
    dsimp only
    exact abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hu.1) (Real.exp_pos _).le)
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hc.abs.intervalIntegrable (0 : ℝ) 1)
      (hc.abs.intervalIntegrable (1 : ℝ) (247 / 100)),
    hl, hr, left_density_integral, left_density_integral]
  nlinarith only [exp_neg_one_le_three_eighths, (Real.exp_pos (-(247 / 100 : ℝ))).le]

/-- On the short ramp, the absolute joint density 2Qmiddle-Qleft is at most twice the absolute
middle density. Its polynomial-exponential factor is nonnegative there. This permits taking
the norm only after the common principal contribution has been subtracted. -/
theorem ramp_joint_middle_abs_le {u : ℝ} (hu : (247 / 100 : ℝ) ≤ u) (hub : u ≤ 99 / 40) :
    |2 * exponentialRampVariationMiddle u - exponentialRampVariationLeft u| ≤
      2 * |exponentialRampVariationMiddle u| := by
  have hp : 0 ≤ (u - 1) * ((99 / 40 - u) / (1 / 200 : ℝ)) :=
    mul_nonneg (by linarith only [hu]) (div_nonneg (sub_nonneg.mpr hub) (by norm_num only))
  have he :
    2 * exponentialRampVariationMiddle u - exponentialRampVariationLeft u =
      Real.exp (-u) * (2 * ((u - 1) * ((99 / 40 - u) / (1 / 200 : ℝ))) + (799 * u - 399)) := by
    dsimp only [exponentialRampVariationMiddle, exponentialRampVariationLeft]
    ring
  have hj : 0 ≤ 2 * exponentialRampVariationMiddle u - exponentialRampVariationLeft u := by
    rw [he]
    exact mul_nonneg (Real.exp_pos _).le (by linarith only [hp, hu])
  have hl : 0 ≤ exponentialRampVariationLeft u :=
    mul_nonneg (by linarith only [hu]) (Real.exp_pos _).le
  rw [abs_of_nonneg hj]
  linarith only [hl, le_abs_self (exponentialRampVariationMiddle u)]

/-- The middle variation density is continuous as a polynomial-exponential expression.
This supplies integrability for the joint smooth-density comparison. -/
theorem ramp_middle_density_continuous : Continuous exponentialRampVariationMiddle := by
  exact
    (Real.continuous_exp.comp continuous_id.neg).mul
      (((continuous_id.sub continuous_const).mul
            ((continuous_const.sub continuous_id).div_const (1 / 200))).add
        (((continuous_const.mul continuous_id).sub continuous_const).div_const (1 / 200)))

/-- The joint middle density is continuous. Combine continuity of the ramp and principal
densities. This is the integrability input for its finite-interval norm bound. -/
theorem ramp_joint_middle_density_continuous :
    Continuous (fun u ↦ 2 * exponentialRampVariationMiddle u - exponentialRampVariationLeft u) := by
  exact
    (continuous_const.mul ramp_middle_density_continuous).sub
      ((continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg))

/-- The absolute joint middle density integrates to at most seven tenths. Integrate its
pointwise domination by twice the middle density. This is the compact smooth cost after
combining the ramp and principal errors. -/
theorem ramp_joint_middle_abs_integral_le :
    (∫ u in (247 / 100 : ℝ)..(99 / 40),
        |2 * exponentialRampVariationMiddle u - exponentialRampVariationLeft u|) ≤
      7 / 10 := by
  have h :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40)
      (ramp_joint_middle_density_continuous.abs.intervalIntegrable _ _)
      ((continuous_const.mul ramp_middle_density_continuous.abs).intervalIntegrable _ _)
      (fun u hu ↦ ramp_joint_middle_abs_le hu.1 hu.2)
  simp only [Pi.mul_apply] at h
  rw [intervalIntegral.integral_const_mul] at h
  linarith only [h, ramp_middle_abs_integral_le_seven_twentieths]

/-- For nonnegative affine coefficients A,B and endpoint y at least 99/40, the exponential
variation tail is at most (21/100)A+(13/16)B. Evaluate the quadratic primitive and retain the
nonnegative endpoint remainder. This bounds only the tail left after compact cancellation. -/
theorem integral_affine_exponential_tail_le {A B y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hy : (99 / 40 : ℝ) ≤ y) :
    (∫ u in (99 / 40 : ℝ)..y, (A + B * u) * (u - 1) * Real.exp (-u)) ≤
      (21 / 100 : ℝ) * A + (13 / 16 : ℝ) * B := by
  let f := fun u : ℝ ↦ (A + B * u) * (u - 1) * Real.exp (-u)
  have hc : Continuous f :=
    ((continuous_const.add (continuous_const.mul continuous_id)).mul
          (continuous_id.sub continuous_const)).mul
      (Real.continuous_exp.comp continuous_id.neg)
  have he : f = fun u : ℝ ↦ (-A + (A - B) * u + B * u ^ 2) * Real.exp (-u) := by
    funext u
    dsimp only [f]
    ring
  have hj :=
    intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
      (hc.intervalIntegrable (0 : ℝ) (99 / 40)) (hc.intervalIntegrable (99 / 40 : ℝ) y)
  rw [he, integral_exponential_quadratic, integral_exponential_quadratic] at hj
  have hy0 : 0 ≤ y := by linarith only [hy]
  have ht : 0 ≤ (A * y + B * (y ^ 2 + y + 1)) * Real.exp (-y) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    nlinarith only [mul_nonneg hA hy0, mul_nonneg hB (sq_nonneg y), mul_nonneg hB hy0, hB]
  have hb : 0 ≤ A * (99 / 40 : ℝ) + B * ((99 / 40 : ℝ) ^ 2 + 99 / 40 + 1) := by
    linarith only [hA, hB]
  have hp :=
    mul_le_mul_of_nonneg_left
      ((Real.exp_le_exp.mpr (by norm_num only : -(99 / 40 : ℝ) ≤ -(247 / 100))).trans
        ramp_exp_left_le)
      hb
  change (∫ u in (99 / 40 : ℝ)..y, f u) ≤ _
  rw [he]
  nlinarith only [hj, ht, hp, hA, hB]

/-- On an ordered real interval, continuous factors and a uniform bound M on the first factor
give the displayed absolute integral bound. Apply integral norm domination and monotonicity.
Only interval continuity is required, so arithmetic errors need no global extension. -/
theorem abs_integral_mul_le_of_continuousOn {f Q : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.uIcc a b)) (hQ : ContinuousOn Q (Set.uIcc a b))
    (hbound : ∀ u ∈ Set.Icc a b, |f u| ≤ M) :
    |∫ u in a..b, f u * Q u| ≤ M * ∫ u in a..b, |Q u| := by
  have hn :=
    intervalIntegral.norm_integral_le_integral_norm (f := fun u ↦ f u * Q u) (μ :=
      MeasureTheory.volume) hab
  simp only [Real.norm_eq_abs] at hn
  have hi :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
      ((hf.mul hQ).abs.intervalIntegrable)
      ((continuous_const.continuousOn.mul hQ.abs).intervalIntegrable)
      (fun u hu ↦
        show |f u * Q u| ≤ M * |Q u| from by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hbound u hu) (abs_nonneg _))
  simp only [Pi.mul_apply] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  exact hn.trans hi

end PseudoPrime.Analysis
