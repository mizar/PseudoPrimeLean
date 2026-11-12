/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.LinearCombination

/-! # Integrals of logarithmic linear expressions -/

public section

namespace PseudoPrime.Analysis

/-- For positive ordered endpoints, integrate the generic logarithmic
zero-count main term divided by the squared height. Differentiate its explicit
primitive; the parameters are unrestricted real constants. -/
theorem integral_log_linear_div_sq {a b k c d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, (k * t * (Real.log t - c - 1) + d) / t ^ 2) =
      (k / 2 * (Real.log b - c) ^ 2 - k * (Real.log b - c) - d / b) -
        (k / 2 * (Real.log a - c) ^ 2 - k * (Real.log a - c) - d / a) := by
  have hi :
    IntervalIntegrable (fun t : ℝ ↦ (k * t * (Real.log t - c - 1) + d) / t ^ 2) MeasureTheory.volume
      a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hlog := Real.continuousAt_log ht0
    exact
      (((continuousAt_const.mul continuousAt_id).mul
                ((hlog.sub continuousAt_const).sub continuousAt_const)).add
            continuousAt_const |>.div
          (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)).continuousWithinAt
  have hd :
    ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x : ℝ ↦ k / 2 * (Real.log x - c) ^ 2 - k * (Real.log x - c) - d / x)
        ((k * t * (Real.log t - c - 1) + d) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have hl := (Real.hasDerivAt_log ht0).sub_const c
    have h1 := ((hl.pow 2).const_mul (k / 2)).sub (hl.const_mul k)
    have h2 := (hasDerivAt_const t d).div (hasDerivAt_id t) ht0
    have h := h1.sub h2
    convert h using 1
    · funext x
      rfl
    · dsimp only [id_eq]
      have hcancel := mul_inv_cancel₀ ht0
      simp only [div_eq_mul_inv, ← inv_pow]
      linear_combination (k * (Real.log t - c - 1) * t⁻¹) * hcancel
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]

/-- Combine the upper endpoint of the generic logarithmic main term with
its inverse-square integral. The upper logarithmic linear terms cancel. -/
theorem log_linear_div_sq_boundary {a b k c d : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (k * b * (Real.log b - c - 1) + d) / b +
        (∫ t in a..b, (k * t * (Real.log t - c - 1) + d) / t ^ 2) =
      k / 2 * ((Real.log b - c) ^ 2 - (Real.log a - c) ^ 2) + k * (Real.log a - c - 1) + d / a := by
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hab)
  have h := integral_log_linear_div_sq (k := k) (c := c) (d := d) ha hab
  rw [h]
  have hcancel := mul_inv_cancel₀ hb0
  simp only [div_eq_mul_inv]
  linear_combination (k * (Real.log b - c - 1)) * hcancel

end PseudoPrime.Analysis
