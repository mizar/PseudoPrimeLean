/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampCutoff
public import PseudoPrime.Analysis.FixedPointExponentialIntervals
public import PseudoPrime.LLS.AnchoredEuler128

/-! # Certified ramp mass for finite-scale principal comparisons -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The negative exponential at the left ramp endpoint is at most 8458486/10^8.
Use the outward fixed-point upper Taylor evaluator at scale 10^12 and twenty terms,
then check its integer endpoint in the kernel. This supplies a sharp mass bound. -/
theorem exp_neg_ramp_left_le : Real.exp (-(247 / 100 : ℝ)) ≤ (8458486 / 100000000 : ℝ) := by
  have h := expNegFixedUpper_ge 247 100 1000000000000 20 (by norm_num only) (by norm_num only)
  have hc : expNegFixedUpper 247 100 1000000000000 20 ≤ 84584860000 := by decide +kernel
  have hr := Nat.cast_le (α := ℝ).mpr hc
  norm_num only [Nat.cast_ofNat, neg_div] at h hr
  linarith only [h, hr]

/-- The negative exponential at the right ramp endpoint is at least 8416299/10^8.
Use the outward fixed-point lower Taylor evaluator with twenty terms and verify
the integer endpoint in the kernel. This supplies the other mass endpoint. -/
theorem exp_neg_ramp_right_ge : (8416299 / 100000000 : ℝ) ≤ Real.exp (-(99 / 40 : ℝ)) := by
  have h :=
    expNegFixedLower_le 99 40 1000000000000 20 (by norm_num only) (by norm_num only)
      (by norm_num only)
  have hc : 84162990000 ≤ expNegFixedLower 99 40 1000000000000 20 := by decide +kernel
  have hr := Nat.cast_le (α := ℝ).mpr hc
  norm_num only [Nat.cast_ofNat, neg_div] at h hr
  linarith only [h, hr]

/-- Twice the actual ramp mass minus one is at least 133/160.
Insert the two certified exponential endpoints into the exact mass formula.
This sharpens the former 821/1000 main-term coefficient without numerical integration. -/
theorem ramp_mass_coefficient_ge_133_160 :
    (133 / 160 : ℝ) ≤ 2 * (∫ u in (0 : ℝ)..(99 / 40), exponentialRampWeight u) - 1 := by
  rw [exponentialRampWeight_integral]
  linarith only [exp_neg_ramp_left_le, exp_neg_ramp_right_ge]

end PseudoPrime.Analysis
