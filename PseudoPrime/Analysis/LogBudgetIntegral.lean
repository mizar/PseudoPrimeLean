/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination

/-! # Integrals of logarithmic count budgets -/

public section

namespace PseudoPrime.Analysis

/-- Integrate a logarithmic budget `(α * log t + β + γ / t) / t²`
for positive ordered endpoints. Its explicit primitive is used in Abel summation
for zero counts, retaining the inverse-height contribution. -/
theorem integral_log_budget_div_sq {a b α β γ : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (α * Real.log t + β + γ / t) / t ^ 2) =
      (α * (Real.log a + 1) + β) / a + γ / (2 * a ^ 2) -
        ((α * (Real.log b + 1) + β) / b + γ / (2 * b ^ 2)) := by
  have hi :
    IntervalIntegrable (fun t : ℝ ↦ (α * Real.log t + β + γ / t) / t ^ 2) MeasureTheory.volume a
      b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    exact
      (((continuousAt_const.mul (Real.continuousAt_log ht0)).add continuousAt_const).add
            (continuousAt_const.div continuousAt_id ht0) |>.div
          (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)).continuousWithinAt
  have hd :
    ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ -((α * (Real.log x + 1) + β) / x + γ / (2 * x ^ 2)))
        ((α * Real.log t + β + γ / t) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have h1 := (((Real.hasDerivAt_log ht0).add_const 1).const_mul α).add_const β
    have h2 := h1.div (hasDerivAt_id t) ht0
    have h3 :=
      (hasDerivAt_const t γ).div (((hasDerivAt_id t).pow 2).const_mul 2)
        (mul_ne_zero (by norm_num only) (pow_ne_zero 2 ht0))
    have h := (h2.add h3).neg
    convert h using 1
    · funext x
      rfl
    · dsimp only [id_eq, Pi.pow_apply]
      norm_num only [Nat.reduceSub, pow_one, zero_mul, sub_zero, mul_one]
      have hc := mul_inv_cancel₀ ht0
      simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
      norm_num only [mul_pow, inv_pow]
      linear_combination (α * t⁻¹ ^ 2) * hc - (γ * t⁻¹ ^ 3) * hc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- Combining the endpoint budget with its integral cancels its upper logarithm
and constant term. This form supplies the reciprocal zero-count estimate. -/
theorem log_budget_div_sq_boundary {a b α β γ : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (α * Real.log b + β + γ / b) / b + (∫ t in a..b, (α * Real.log t + β + γ / t) / t ^ 2) =
      (α * (Real.log a + 1) + β) / a + γ / (2 * a ^ 2) - α / b + γ / (2 * b ^ 2) := by
  rw [integral_log_budget_div_sq ha hab]
  simp only [div_eq_mul_inv]
  ring

/-- Integrate a logarithmic count budget against twice the inverse-cube kernel
on positive ordered endpoints. The antiderivative retains the inverse-height
term needed for an explicit inverse-square tail estimate. -/
theorem integral_log_budget_inv_cube {a b α β γ : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (α * Real.log t + β + γ / t) * (2 * t⁻¹ ^ 3)) =
      ((α * (Real.log a + 1 / 2) + β) / a ^ 2 + 2 * γ / (3 * a ^ 3)) -
        ((α * (Real.log b + 1 / 2) + β) / b ^ 2 + 2 * γ / (3 * b ^ 3)) := by
  have hi :
    IntervalIntegrable (fun t : ℝ ↦ (α * Real.log t + β + γ / t) * (2 * t⁻¹ ^ 3))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    exact
      ((((continuousAt_const.mul (Real.continuousAt_log ht0)).add continuousAt_const).add
              (continuousAt_const.div continuousAt_id ht0)).mul
          (continuousAt_const.mul ((continuousAt_id.inv₀ ht0).pow 3))).continuousWithinAt
  have hd :
    ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ -((α * (Real.log x + 1 / 2) + β) / x ^ 2 + 2 * γ / (3 * x ^ 3)))
        ((α * Real.log t + β + γ / t) * (2 * t⁻¹ ^ 3)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have h1 := (((Real.hasDerivAt_log ht0).add_const (1 / 2)).const_mul α).add_const β
    have h2 := h1.div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0)
    have h3 :=
      (hasDerivAt_const t (2 * γ)).div (((hasDerivAt_id t).pow 3).const_mul 3)
        (mul_ne_zero (by norm_num only) (pow_ne_zero 3 ht0))
    have h := (h2.add h3).neg
    convert h using 1
    · funext x
      rfl
    · dsimp only [id_eq, Pi.pow_apply]
      norm_num only [Nat.reduceSub, pow_one, zero_mul, sub_zero, mul_one]
      have hc := mul_inv_cancel₀ ht0
      simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
      norm_num only [mul_pow, inv_pow]
      linear_combination
        (α * t⁻¹ ^ 3 - 2 * γ * t⁻¹ ^ 4 - 2 * α * Real.log t * t⁻¹ ^ 3 +
              α * t⁻¹ ^ 3 * (t * t⁻¹ - 1) -
            2 * β * t⁻¹ ^ 3 -
            2 * γ * t * t⁻¹ ^ 5) *
          hc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- Integrate a logarithmic zero-count main term against the inverse-cube
kernel on a positive interval. Its primitive supplies the main contribution
to a finite zero-tail estimate. -/
theorem integral_log_main_inv_cube {a b k c d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (k * t * (Real.log t - c - 1) + d) * (2 * t⁻¹ ^ 3)) =
      (-2 * k * (Real.log b - c) / b - d / b ^ 2) -
        (-2 * k * (Real.log a - c) / a - d / a ^ 2) := by
  have hi :
    IntervalIntegrable (fun t : ℝ ↦ (k * t * (Real.log t - c - 1) + d) * (2 * t⁻¹ ^ 3))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    exact
      ((((continuousAt_const.mul continuousAt_id).mul
                  (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
              continuousAt_const).mul
          (continuousAt_const.mul ((continuousAt_id.inv₀ ht0).pow 3))).continuousWithinAt
  have hd :
    ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ -2 * k * (Real.log x - c) / x - d / x ^ 2)
        ((k * t * (Real.log t - c - 1) + d) * (2 * t⁻¹ ^ 3)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hl := Real.hasDerivAt_log ht0
    have h1 := (((hl.sub_const c).const_mul (-2 * k)).div (hasDerivAt_id t) ht0)
    have h2 := (hasDerivAt_const t d).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht0)
    have h := h1.sub h2
    convert h using 1
    · funext x
      rfl
    · dsimp only [Pi.pow_apply, id_eq]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_mul, sub_zero, mul_one]
      have hc := mul_inv_cancel₀ ht0
      simp only [div_eq_mul_inv, ← inv_pow]
      linear_combination (-2 * d * t⁻¹ ^ 3 + 2 * k * (Real.log t - c) * t⁻¹ ^ 2) * hc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]

end PseudoPrime.Analysis
