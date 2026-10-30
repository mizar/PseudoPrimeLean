/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

/-! # Exact second and third Cauchy power integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For natural n>=1, the function 1/(1+t^2)^n is integrable on the real line.
Dominate it by the known Cauchy weight, using the base >=1 and continuity.
This provides absolute integrability for the fourth- and sixth-order kernel masses. -/
theorem integrable_cauchy_power {n : ℕ} (hn : 1 ≤ n) :
    MeasureTheory.Integrable (fun t : ℝ ↦ 1 / (1 + t  ^  2)  ^  n) := by
  apply MeasureTheory.Integrable.mono' integrable_inv_one_add_sq
  · exact (continuous_const.div ((continuous_const.add (continuous_id.pow 2)).pow n)
      (fun t ↦ pow_ne_zero _ (ne_of_gt
      (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      have hB : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith only [sq_nonneg t]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg zero_le_one (pow_nonneg (by linarith only [hB]) _))]
      have hp : 1 + t ^ 2 ≤ (1 + t ^ 2) ^ n := by
        simpa only [pow_one] using pow_le_pow_right₀ hB hn
      rw [← one_div]
      exact div_le_div_of_nonneg_left zero_le_one (by linarith only [hB]) hp

/-- The rational function t/(1+t^2) equals t^-1/(1+t^-2), including t=0.
Separate zero and clear the explicitly nonzero denominators. This rewrites both
infinite-endpoint limits as continuous functions of the vanishing reciprocal. -/
private theorem cauchyRatio_eq_inverse_ratio (t : ℝ) : t / (1 + t ^ 2) = t⁻¹ / (1 + (t⁻¹) ^ 2) := by
  by_cases ht : t = 0
  · simp only [ht, inv_zero, zero_pow (by norm_num only : 2 ≠ 0), add_zero, zero_div]
  · have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2)
    have hdi : 1 + (t⁻¹) ^ 2 ≠ 0 :=
      ne_of_gt (by nlinarith only [sq_nonneg (t⁻¹)] : (0 : ℝ) < 1 + (t⁻¹) ^ 2)
    field_simp (disch := first | exact ht | exact hd | exact hdi)
    rw [add_comm (t  ^  2) 1, div_self hd]

/-- A vanishing reciprocal gives a vanishing inverse Cauchy ratio by continuity.
Divide by a denominator tending to one. This is used at both infinite endpoints. -/
private theorem tendsto_inverse_cauchyRatio {l : Filter ℝ}
    (hi : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) l (nhds 0)) :
    Filter.Tendsto (fun t : ℝ ↦ t⁻¹ / (1 + (t⁻¹) ^ 2)) l (nhds 0) := by
  have h := hi.div (tendsto_const_nhds.add (hi.pow 2))
    (by norm_num only : (1 : ℝ) + 0 ^ 2 ≠ 0)
  have hh : Filter.Tendsto ((fun t : ℝ ↦ t⁻¹) / (fun t : ℝ ↦ 1 + (t⁻¹) ^ 2)) l
      (nhds (0 : ℝ)) := by
    simpa only [zero_pow (by norm_num only : 2 ≠ 0), add_zero, zero_div] using h
  exact hh.congr' (Filter.Eventually.of_forall fun t ↦ rfl)

/-- The derivative of t/(1+t^2) is 2/(1+t^2)^2-1/(1+t^2).
Differentiate the quotient and normalize rational expressions with their positive
denominator. Integrating this identity determines the second Cauchy moment. -/
private theorem hasDerivAt_cauchyRatio (t : ℝ) : HasDerivAt (fun u : ℝ ↦ u / (1 + u ^ 2))
    (2 * (1 / (1 + t ^ 2) ^ 2) - 1 / (1 + t ^ 2)) t := by
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2)
  convert (hasDerivAt_id t).div ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)) hd using 1
  · rfl
  · simp only [Pi.add_apply, Pi.pow_apply, id_eq, one_mul, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one, zero_add]
    field_simp (disch := exact hd)
    ring

/-- The derivative of t/(1+t^2)^2 is 4/(1+t^2)^3-3/(1+t^2)^2.
Apply the quotient and power rules and clear known nonzero denominators.
This recurrence determines the third Cauchy moment from the second. -/
private theorem hasDerivAt_cauchyRatio_sq (t : ℝ) : HasDerivAt (fun u : ℝ ↦ u / (1 + u ^ 2) ^ 2)
    (4 * (1 / (1 + t ^ 2) ^ 3) - 3 * (1 / (1 + t ^ 2) ^ 2)) t := by
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2)
  convert (hasDerivAt_id t).div
    (((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2)).pow 2) (pow_ne_zero 2 hd) using 1
  · rfl
  · simp only [Pi.pow_apply, Pi.add_apply, id_eq, one_mul, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, mul_one, zero_add]
    field_simp (disch := first | exact hd | exact pow_ne_zero 2 hd)
    ring

/-- The exact full-line integral of 1/(1+t^2)^2 is pi/2.
Integrate the rational derivative identity with vanishing endpoint limits and use
the known Cauchy integral pi. This gives the fourth-order Mellin kernel mass. -/
theorem integral_cauchy_power_two : (∫ t : ℝ, 1 / (1 + t ^ 2) ^ 2) = Real.pi / 2 := by
  have hi1 : MeasureTheory.Integrable (fun t : ℝ ↦ 1 / (1 + t ^ 2)) := by
    simpa only [pow_one] using integrable_cauchy_power (by norm_num only : 1 ≤ 1)
  have hi2 := integrable_cauchy_power (by norm_num only : 1 ≤ 2)
  have ht : Filter.Tendsto (fun t : ℝ ↦ t / (1 + t ^ 2)) Filter.atTop (nhds 0) :=
    (tendsto_inverse_cauchyRatio tendsto_inv_atTop_zero).congr'
      (Filter.Eventually.of_forall fun t ↦ (cauchyRatio_eq_inverse_ratio t).symm)
  have hb : Filter.Tendsto (fun t : ℝ ↦ t / (1 + t ^ 2)) Filter.atBot (nhds 0) :=
    (tendsto_inverse_cauchyRatio tendsto_inv_atBot_zero).congr'
      (Filter.Eventually.of_forall fun t ↦ (cauchyRatio_eq_inverse_ratio t).symm)
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto hasDerivAt_cauchyRatio
    ((hi2.const_mul 2).sub hi1) hb ht
  rw [MeasureTheory.integral_sub (hi2.const_mul 2) hi1, MeasureTheory.integral_const_mul] at h
  have hi : (∫ t : ℝ, 1 / (1 + t ^ 2)) = Real.pi := by
    simpa only [one_div] using integral_univ_inv_one_add_sq
  rw [hi, sub_self] at h
  linarith only [h]

/-- The rational function t/(1+t^2)^2 is integrable. Use |t|<=1+t^2
and dominate its norm by the Cauchy weight. This removes both endpoint terms
when integrating its derivative for the third Cauchy moment. -/
private theorem integrable_cauchyRatio_sq :
    MeasureTheory.Integrable (fun t : ℝ ↦ t / (1 + t ^ 2) ^ 2) := by
  have hi : MeasureTheory.Integrable (fun t : ℝ ↦ 1 / (1 + t ^ 2)) := by
    simpa only [pow_one] using integrable_cauchy_power (by norm_num only : 1 ≤ 1)
  apply hi.mono'
  · exact ((continuous_id.div ((continuous_const.add (continuous_id.pow 2)).pow 2)
      (fun t ↦ pow_ne_zero 2 (ne_of_gt
        (by nlinarith only [sq_nonneg t] : (0 : ℝ) < 1 + t ^ 2))))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      have hp : 0 < 1 + t ^ 2 := by nlinarith only [sq_nonneg t]
      have ha : |t| ≤ 1 + t ^ 2 := by
        nlinarith only [sq_nonneg (|t| - 1), sq_abs t, abs_nonneg t]
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hp 2)]
      have h := div_le_div_of_nonneg_right ha (sq_nonneg (1 + t ^ 2))
      have he : (1 + t ^ 2) / (1 + t ^ 2) ^ 2 = 1 / (1 + t ^ 2) := by
        rw [pow_two (1 + t ^ 2), div_mul_eq_div_div, div_self hp.ne']
      rw [he] at h
      exact h

/-- The exact full-line integral of 1/(1+t^2)^3 is 3pi/8.
Integrate the derivative of the integrable squared-denominator ratio and insert
the second moment. This gives the sixth-order Mellin kernel mass. -/
theorem integral_cauchy_power_three : (∫ t : ℝ, 1 / (1 + t ^ 2) ^ 3) = 3 * Real.pi / 8 := by
  have hi2 := integrable_cauchy_power (by norm_num only : 1 ≤ 2)
  have hi3 := integrable_cauchy_power (by norm_num only : 1 ≤ 3)
  have h := MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable hasDerivAt_cauchyRatio_sq
    ((hi3.const_mul 4).sub (hi2.const_mul 3)) integrable_cauchyRatio_sq
  rw [MeasureTheory.integral_sub (hi3.const_mul 4) (hi2.const_mul 3),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_cauchy_power_two] at h
  linarith only [h]
end PseudoPrime.Analysis
