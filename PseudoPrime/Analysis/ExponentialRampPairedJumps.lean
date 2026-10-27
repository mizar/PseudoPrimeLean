/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampVariationBounds

/-! # Pairing the signed ramp jumps before taking absolute values -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Magnitude of the derivative jump at the left ramp endpoint 247/100.
It is the coefficient of the negative boundary term in the variation functional. -/
noncomputable def rampLeftJump : ℝ :=
  (247 / 100) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200)

/-- Magnitude of the derivative jump at the right ramp endpoint 99/40.
It weights the anchored increment when the signed boundary terms are paired. -/
noncomputable def rampRightJump : ℝ :=
  (99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200)

/-- The two positive derivative jumps differ by a number between zero
and 1/8. Integrate the left variation density across the short ramp and use
its exponential endpoint bound. This preserves cancellation of the jumps. -/
theorem ramp_jump_difference_bounds :
    0 ≤ rampLeftJump - rampRightJump ∧ rampLeftJump - rampRightJump ≤ 1 / 8 := by
  have hcont : Continuous exponentialRampVariationLeft :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hn : 0 ≤ ∫ u in (247 / 100 : ℝ)..(99 / 40), exponentialRampVariationLeft u := by
    apply intervalIntegral.integral_nonneg (by norm_num only)
    intro u hu
    exact mul_nonneg (by linarith only [hu.1]) (Real.exp_pos _).le
  have hb :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40)
      (hcont.intervalIntegrable (247 / 100) (99 / 40))
      (continuous_const.intervalIntegrable (247 / 100) (99 / 40)) (g := fun _ ↦
      (99 / 40 - 1) * Real.exp (-(247 / 100 : ℝ)))
      (fun u hu ↦ by
        exact
          mul_le_mul (sub_le_sub_right hu.2 1) (Real.exp_le_exp.mpr (neg_le_neg hu.1))
            (Real.exp_pos _).le (by norm_num only))
  rw [left_density_integral] at hn hb
  rw [intervalIntegral.integral_const, smul_eq_mul] at hb
  unfold rampLeftJump rampRightJump
  constructor <;> nlinarith only [hn, hb, ramp_exp_left_le]

/-- The right derivative jump is nonnegative and at most 42.
Use the exponential upper bound at the left endpoint.
This is the coefficient of the short-ramp increment in the paired estimate. -/
theorem ramp_right_jump_bounds : 0 ≤ rampRightJump ∧ rampRightJump ≤ 42 := by
  have he :=
    (Real.exp_le_exp.mpr (by norm_num only : -(99 / 40 : ℝ) ≤ -(247 / 100))).trans ramp_exp_left_le
  unfold rampRightJump
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num only) (Real.exp_pos _).le) (by norm_num only)
  · nlinarith only [he]

/-- The middle absolute variation mass is at most 7/20.
Combine the existing density integral bound with the exponential certificate.
This controls the smooth ramp part without charging either jump separately. -/
theorem ramp_middle_abs_integral_le_seven_twentieths :
    (∫ u in (247 / 100 : ℝ)..(99 / 40), |exponentialRampVariationMiddle u|) ≤ 7 / 20 := by
  have h := middle_abs_integral_le
  have he := ramp_exp_left_le
  nlinarith only [h, he]

/-- Given a bound M on the left value and D on its increment, the signed
jump pair is at most M/8+42D in absolute value. Rewrite it as a small jump
difference times the anchor plus the right jump times the increment.
This replaces the sum of the two large absolute jump allowances. -/
theorem ramp_paired_jumps_abs_le {a b M D : ℝ} (ha : |a| ≤ M) (hd : |b - a| ≤ D) :
    |-(a * rampLeftJump) + b * rampRightJump| ≤ M / 8 + 42 * D := by
  have hj := ramp_jump_difference_bounds
  have hr := ramp_right_jump_bounds
  have hM := (abs_nonneg a).trans ha
  have hD := (abs_nonneg (b - a)).trans hd
  have h1 := mul_le_mul ha hj.2 hj.1 hM
  have h2 := mul_le_mul hd hr.2 hr.1 hD
  have ht := abs_sub ((b - a) * rampRightJump) (a * (rampLeftJump - rampRightJump))
  rw [abs_mul, abs_mul, abs_of_nonneg hr.1, abs_of_nonneg hj.1] at ht
  have he :
    -(a * rampLeftJump) + b * rampRightJump =
      (b - a) * rampRightJump - a * (rampLeftJump - rampRightJump) := by
    ring
  rw [he]
  nlinarith only [h1, h2, ht]

end PseudoPrime.Analysis
