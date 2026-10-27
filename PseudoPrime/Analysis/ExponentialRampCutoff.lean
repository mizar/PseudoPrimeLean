/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

/-! # Exponential ramp cutoff with exact mass and derivative jumps -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The exponential lower cutoff with left endpoint 247/100, right endpoint 99/40,
and ramp width 1/200. It equals exp(-u) before the ramp, decreases linearly relative
to that exponential on the ramp, and vanishes at and after the right endpoint.
This continuous weight is used only on the principal finite sum. -/
noncomputable def exponentialRampWeight (u : ℝ) : ℝ :=
  if u ≤ 247 / 100 then Real.exp (-u)
  else if u ≤ 99 / 40 then Real.exp (-u) * (99 / 40 - u) / (1 / 200) else 0

/-- For u <= 247/100 the ramp weight equals exp(-u). Unfold the first branch.
This identifies the left piece when computing its mass and partial summation. -/
theorem exponentialRampWeight_eq_exp_of_le_left {u : ℝ} (hu : u ≤ 247 / 100) :
    exponentialRampWeight u = Real.exp (-u) := by exact ite_eq_left hu

/-- On the closed ramp interval, the weight equals its polynomial-exponential
branch. At the left endpoint both formulas agree; otherwise select the second branch.
This also covers integer cutoffs coinciding with a join. -/
theorem exponentialRampWeight_eq_middle {u : ℝ} (hl : 247 / 100 ≤ u) (hr : u ≤ 99 / 40) :
    exponentialRampWeight u = Real.exp (-u) * (99 / 40 - u) / (1 / 200) := by
  by_cases hu : u ≤ 247 / 100
  · have heq : u = 247 / 100 := le_antisymm hu hl
    rw [exponentialRampWeight, ite_eq_left hu, heq]
    ring
  · exact ite_eq_right hu |>.trans (ite_eq_left hr)

/-- At and after 99/40 the weight vanishes. Select the zero branch, or use the
zero numerator at the endpoint. This gives the support bound for the witness cutoff. -/
theorem exponentialRampWeight_eq_zero {u : ℝ} (hu : 99 / 40 ≤ u) : exponentialRampWeight u = 0 := by
  have hleft : ¬u ≤ 247 / 100 := by linarith only [hu]
  by_cases hr : u ≤ 99 / 40
  · have heq : u = 99 / 40 := le_antisymm hr hu
    rw [exponentialRampWeight, ite_eq_right hleft, ite_eq_left hr, heq]
    simp only [sub_self, mul_zero, zero_div]
  · simp only [exponentialRampWeight, ite_eq_right hleft, ite_eq_right hr]

/-- At every real u, the ramp weight lies between zero and exp(-u).
The ramp factor is between zero and one; the other branches are immediate.
This supplies the pointwise comparison used in the no-witness argument. -/
theorem exponentialRampWeight_bounds (u : ℝ) :
    0 ≤ exponentialRampWeight u ∧ exponentialRampWeight u ≤ Real.exp (-u) := by
  by_cases hl : u ≤ 247 / 100
  · rw [exponentialRampWeight_eq_exp_of_le_left hl]
    exact ⟨(Real.exp_pos _).le, le_rfl⟩
  · by_cases hr : u ≤ 99 / 40
    · rw [exponentialRampWeight_eq_middle (le_of_not_ge hl) hr]
      constructor
      · exact div_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hr)) (by norm_num only)
      · have h :=
          mul_le_mul_of_nonneg_left
            (show 99 / 40 - u ≤ (1 / 200 : ℝ) by linarith only [le_of_not_ge hl])
            (Real.exp_pos (-u)).le
        exact (div_le_iff₀ (by norm_num only : (0 : ℝ) < 1 / 200)).mpr h
    · rw [exponentialRampWeight_eq_zero (le_of_not_ge hr)]
      exact ⟨le_rfl, (Real.exp_pos _).le⟩

/-- At any u, the displayed polynomial-exponential primitive has derivative
exp(-u)(99/40-u)/(1/200). Differentiate its product and divide by the constant width.
This evaluates the exact ramp mass without a numerical integration premise. -/
theorem exponentialRamp_middle_primitive (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-v) * (v + 1 - 99 / 40) / (1 / 200))
      (Real.exp (-u) * (99 / 40 - u) / (1 / 200)) u := by
  have h :=
    (((hasDerivAt_id u).neg.exp).mul
          (((hasDerivAt_id u).add_const 1).sub_const (99 / 40))).div_const
      (1 / 200)
  change
    HasDerivAt (fun v : ℝ ↦ Real.exp (-v) * (v + 1 - 99 / 40) / (1 / 200))
      ((Real.exp (-u) * (-1) * (u + 1 - 99 / 40) + Real.exp (-u) * 1) / (1 / 200)) u at h
  exact h.congr_deriv (by ring)

/-- The ramp weight is interval integrable on [0,247/100]. Replace it by the
continuous exponential branch. This permits splitting the mass integral at the join. -/
private theorem exponentialRamp_left_integrable :
    IntervalIntegrable exponentialRampWeight MeasureTheory.volume 0 (247 / 100) := by
  apply
    IntervalIntegrable.congr _
      ((Real.continuous_exp.comp continuous_id.neg).intervalIntegrable (0 : ℝ) (247 / 100))
  intro u hu
  rw [Set.uIoc_of_le (by norm_num only : (0 : ℝ) ≤ 247 / 100)] at hu
  exact (exponentialRampWeight_eq_exp_of_le_left hu.2).symm

/-- The ramp weight is interval integrable on [247/100,99/40]. Replace it by
the continuous middle branch. This permits adjoining the two finite mass integrals. -/
private theorem exponentialRamp_middle_integrable :
    IntervalIntegrable exponentialRampWeight MeasureTheory.volume (247 / 100) (99 / 40) := by
  apply
    IntervalIntegrable.congr (f := fun u : ℝ ↦ Real.exp (-u) * (99 / 40 - u) / (1 / 200)) _
      ((((Real.continuous_exp.comp continuous_id.neg).mul
                (continuous_const.sub continuous_id)).div_const
            (1 / 200)).intervalIntegrable
        (247 / 100 : ℝ) (99 / 40))
  intro u hu
  rw [Set.uIoc_of_le (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40)] at hu
  exact (exponentialRampWeight_eq_middle hu.1.le hu.2).symm

/-- The exponential integral on [0,247/100] equals 1-exp(-247/100).
Differentiate -exp(-u) and apply the fundamental theorem of calculus.
This is the first piece of the exact ramp mass. -/
private theorem exponentialRamp_first_integral :
    (∫ u in (0 : ℝ)..(247 / 100), Real.exp (-u)) = 1 - Real.exp (-(247 / 100 : ℝ)) := by
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ ↦ -Real.exp (-v)) (Real.exp (-u)) u := by
    have h := (hasDerivAt_id u).neg.exp.neg
    exact
      h.congr_deriv
        (by
          change -(Real.exp (-u) * (-1)) = Real.exp (-u); ring)
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hd u)
      ((Real.continuous_exp.comp continuous_id.neg).intervalIntegrable (0 : ℝ) (247 / 100))
  simp only [neg_zero, Real.exp_zero] at h
  exact h.trans (by ring)

/-- The middle branch integral equals the difference of its explicit primitive
at the two endpoints. Apply the fundamental theorem of calculus.
This is the second piece of the exact ramp mass. -/
private theorem exponentialRamp_second_integral :
    (∫ u in (247 / 100 : ℝ)..(99 / 40), Real.exp (-u) * (99 / 40 - u) / (1 / 200)) =
      (Real.exp (-(99 / 40 : ℝ)) - Real.exp (-(247 / 100 : ℝ)) * (1 - 1 / 200)) / (1 / 200) := by
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ exponentialRamp_middle_primitive u)
      ((((Real.continuous_exp.comp continuous_id.neg).mul
                (continuous_const.sub continuous_id)).div_const
            (1 / 200)).intervalIntegrable
        (247 / 100 : ℝ) (99 / 40))
  exact h.trans (by ring)

/-- The weight integral on the left interval equals the exponential integral.
Use equality of the branches throughout the closed interval.
This connects the mass integral to the explicit first-piece evaluation. -/
private theorem exponentialRamp_left_integral_eq :
    (∫ u in (0 : ℝ)..(247 / 100), exponentialRampWeight u) =
      ∫ u in (0 : ℝ)..(247 / 100), Real.exp (-u) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num only : (0 : ℝ) ≤ 247 / 100)] at hu
  exact exponentialRampWeight_eq_exp_of_le_left hu.2

/-- The weight integral on the middle interval equals the ramp-branch integral.
Use equality of both endpoint values as well as the interior formula.
This connects the mass integral to the explicit second-piece evaluation. -/
private theorem exponentialRamp_middle_integral_eq :
    (∫ u in (247 / 100 : ℝ)..(99 / 40), exponentialRampWeight u) =
      ∫ u in (247 / 100 : ℝ)..(99 / 40), Real.exp (-u) * (99 / 40 - u) / (1 / 200) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40)] at hu
  exact exponentialRampWeight_eq_middle hu.1 hu.2

/-- The actual finite integral of the ramp weight is
1-(exp(-247/100)-exp(-99/40))/(1/200). Split at the left endpoint and evaluate
both polynomial-exponential pieces. This is the smoothed main-term mass. -/
theorem exponentialRampWeight_integral :
    (∫ u in (0 : ℝ)..(99 / 40), exponentialRampWeight u) =
      1 - (Real.exp (-(247 / 100 : ℝ)) - Real.exp (-(99 / 40 : ℝ))) / (1 / 200) := by
  rw [←
    intervalIntegral.integral_add_adjacent_intervals exponentialRamp_left_integrable
      exponentialRamp_middle_integrable]
  rw [exponentialRamp_left_integral_eq, exponentialRamp_middle_integral_eq,
    exponentialRamp_first_integral, exponentialRamp_second_integral]
  ring

/-- At any u, the first smooth branch has derivative -exp(-u).
Differentiate the negative argument. This supplies the left derivative at the join. -/
theorem exponentialRamp_first_derivative (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-v)) (-Real.exp (-u)) u := by
  have h := (hasDerivAt_id u).neg.exp
  exact
    h.congr_deriv
      (by
        change Real.exp (-u) * (-1) = -Real.exp (-u); ring)

/-- At any u, the middle smooth branch has the displayed derivative.
Differentiate the product and divide by the constant width.
This determines the two jumps used in double partial summation. -/
theorem exponentialRamp_middle_derivative (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-v) * (99 / 40 - v) / (1 / 200))
      (Real.exp (-u) * (u - 99 / 40 - 1) / (1 / 200)) u := by
  have h :=
    (((hasDerivAt_id u).neg.exp).mul
          ((hasDerivAt_const u (99 / 40)).sub (hasDerivAt_id u))).div_const
      (1 / 200)
  change
    HasDerivAt (fun v : ℝ ↦ Real.exp (-v) * (99 / 40 - v) / (1 / 200))
      ((Real.exp (-u) * (-1) * (99 / 40 - u) + Real.exp (-u) * (0 - 1)) / (1 / 200)) u at h
  exact h.congr_deriv (by ring)

/-- Differentiate u times the first branch derivative to obtain (u-1)exp(-u).
Use the product rule. This is the first continuous density of the variation kernel. -/
theorem exponentialRamp_first_variation (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ v * (-Real.exp (-v))) ((u - 1) * Real.exp (-u)) u := by
  have h := (hasDerivAt_id u).mul ((exponentialRamp_first_derivative u).neg)
  apply h.congr_deriv
  change 1 * (-Real.exp (-u)) + u * (-(-Real.exp (-u))) = (u - 1) * Real.exp (-u)
  ring

/-- Differentiate u times the middle branch derivative to obtain the displayed
density. Use the product rule and collect the polynomial factors.
This is the middle continuous density of the variation kernel. -/
theorem exponentialRamp_middle_variation (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ v * (Real.exp (-v) * (v - 99 / 40 - 1) / (1 / 200)))
      (Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))) u := by
  have hinner :=
    (((hasDerivAt_id u).neg.exp).mul
          (((hasDerivAt_id u).sub_const (99 / 40)).sub_const 1)).div_const
      (1 / 200)
  have h := (hasDerivAt_id u).mul hinner
  apply h.congr_deriv
  change
    1 * (Real.exp (-u) * (u - 99 / 40 - 1) / (1 / 200)) +
        u * ((Real.exp (-u) * (-1) * (u - 99 / 40 - 1) + Real.exp (-u) * 1) / (1 / 200)) =
      _
  ring

/-- At 247/100, the right value of uW' minus its left value is
-(247/100)exp(-247/100)/(1/200). Check the branch expressions algebraically.
This gives the negative point mass in double partial summation. -/
theorem exponentialRamp_left_jump :
    (247 / 100 : ℝ) *
        (Real.exp (-(247 / 100 : ℝ)) * (247 / 100 - 99 / 40 - 1) / (1 / 200) -
          (-Real.exp (-(247 / 100 : ℝ)))) =
      -(247 / 100 : ℝ) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200) := by
  ring

/-- At 99/40, the zero derivative on the right minus the middle value of uW'
is (99/40)exp(-99/40)/(1/200). Check the branch expressions algebraically.
This gives the positive point mass in double partial summation. -/
theorem exponentialRamp_right_jump :
    (99 / 40 : ℝ) * (0 - Real.exp (-(99 / 40 : ℝ)) * (99 / 40 - 99 / 40 - 1) / (1 / 200)) =
      (99 / 40 : ℝ) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200) := by
  ring

/-- Split the actual ramp mass into the two smooth-branch integrals.
Use integrability and equality on both closed intervals. This is the
main-term identity used when the variation functional is evaluated on u. -/
theorem exponentialRampWeight_integral_eq_branch_sum :
    (∫ u in (0 : ℝ)..(99 / 40), exponentialRampWeight u) =
      (∫ u in (0 : ℝ)..(247 / 100), Real.exp (-u)) +
        ∫ u in (247 / 100 : ℝ)..(99 / 40), Real.exp (-u) * (99 / 40 - u) / (1 / 200) := by
  rw [←
    intervalIntegral.integral_add_adjacent_intervals exponentialRamp_left_integrable
      exponentialRamp_middle_integrable,
    exponentialRamp_left_integral_eq, exponentialRamp_middle_integral_eq]

end PseudoPrime.Analysis
