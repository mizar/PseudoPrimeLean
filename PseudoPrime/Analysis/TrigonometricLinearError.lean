/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Sharp quadratic errors for linear sine and cosine approximations -/

public section

namespace PseudoPrime.Analysis

/-- A continuously differentiable real function whose derivative differs
from its value at a by at most the distance from a has first-order error at
most half the squared distance. Integrating the Lipschitz bound gives the
sharp factor one half for either orientation of the interval. -/
theorem linear_error_of_derivative_bound {f f' : ℝ → ℝ} (a b : ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hc : Continuous f') (hb : ∀ t, |f' t - f' a| ≤ |t - a|) :
    |f b - f a - (b - a) * f' a| ≤ (b - a) ^ 2 / 2 := by
  have hd (t : ℝ) : HasDerivAt (fun u ↦ f u - u * f' a) (f' t - f' a) t := by
    simpa only [id_eq, one_mul] using (hf t).fun_sub ((hasDerivAt_id t).mul_const (f' a))
  have he :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
      ((hc.sub continuous_const).intervalIntegrable a b)
  have hi :=
    intervalIntegral.norm_integral_le_abs_of_norm_le (μ := MeasureTheory.volume) (f := fun t ↦
      f' t - f' a) (g := fun t ↦ |t - a|)
      (Filter.Eventually.of_forall (fun t ↦ by simpa only [Real.norm_eq_abs] using hb t))
      ((continuous_id.sub continuous_const).abs.intervalIntegrable a b)
  rw [intervalIntegral.abs_intervalIntegral_eq] at hi
  have hp := integral_pow_abs_sub_uIoc (a := a) (b := b) (n := 1)
  norm_num only [pow_one] at hp
  rw [hp, sq_abs, he, Real.norm_eq_abs] at hi
  have ha : f b - b * f' a - (f a - a * f' a) = f b - f a - (b - a) * f' a := by ring
  rw [ha] at hi
  have hn : 0 ≤ (b - a) ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num only)
  simpa only [abs_of_nonneg hn] using hi

/-- Linearization of sine at any real center has error at most half the
squared displacement. The proof integrates the global cosine Lipschitz bound;
there is no small-angle restriction or additional exponential factor. -/
theorem sin_linear_error (a b : ℝ) :
    |Real.sin b - Real.sin a - (b - a) * Real.cos a| ≤ (b - a) ^ 2 / 2 := by
  exact
    linear_error_of_derivative_bound a b Real.hasDerivAt_sin Real.continuous_cos
      (fun t ↦ Real.abs_cos_sub_cos_le t a)

/-- Linearization of cosine at any real center has error at most half the
squared displacement. The sine Lipschitz bound controls the negative derivative
and supplies the coordinate error used by finite phase-cell certificates. -/
theorem cos_linear_error (a b : ℝ) :
    |Real.cos b - Real.cos a + (b - a) * Real.sin a| ≤ (b - a) ^ 2 / 2 := by
  have he :=
    linear_error_of_derivative_bound a b Real.hasDerivAt_cos Real.continuous_sin.neg
      (fun t ↦ by
        rw [neg_sub_neg, abs_sub_comm]
        exact Real.abs_sin_sub_sin_le t a)
  simpa only [mul_neg, sub_neg_eq_add] using he

end PseudoPrime.Analysis
