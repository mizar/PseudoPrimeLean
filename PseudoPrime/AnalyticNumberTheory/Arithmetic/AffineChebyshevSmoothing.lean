/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialMangoldtBounds

/-! # Exponential smoothing of global Chebyshev lower envelopes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a positive reference scale x, sqrt(t) lies below its tangent at x
on the whole nonnegative half-line. This keeps both Abel errors on one envelope. -/
theorem sqrt_le_reference_tangent {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    Real.sqrt t ≤ (t + x) / (2 * Real.sqrt x) := by
  apply (le_div_iff₀ (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hx))).mpr
  nlinarith only [sq_nonneg (Real.sqrt t - Real.sqrt x), Real.sq_sqrt ht, Real.sq_sqrt hx.le]

/-- Evaluate an arbitrary affine density against the exponential weight
on a finite nonnegative interval. The exact endpoint permits Abel cancellation. -/
theorem exponential_affine_setIntegral (x A B : ℝ) (hx : x ≠ 0) {y : ℝ} (hy : 0 ≤ y) :
    (∫ t in Set.Ioc 0 y, Real.exp (-t / x) * (A * t + B)) =
      x * (A * x + B) - x * (A * (y + x) + B) * Real.exp (-y / x) := by
  have hd (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ -x * (A * (u + x) + B) * Real.exp (-u / x))
      (Real.exp (-t / x) * (A * t + B)) t := by
    have hp := ((((hasDerivAt_id t).add_const x).const_mul A).add_const B).const_mul (-x)
    have he := ((hasDerivAt_id t).neg.div_const x).exp
    apply (hp.mul he).congr_deriv
    dsimp only [id, Pi.neg_apply]
    field_simp [hx]
    ring
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-t / x) * (A * t + B)) :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const x)).mul
      ((continuous_const.mul continuous_id).add continuous_const)
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) (hc.intervalIntegrable 0 y)
  rw [intervalIntegral.integral_of_le hy] at h
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, zero_add] at h
  nlinarith only [h]

/-- A global affine lower envelope for psi yields a finite exponential
Mangoldt lower bound. No sign condition is imposed on the affine coefficients.
The same envelope is used at the boundary and inside the Abel integral. -/
theorem exponentialMangoldtSum_lower_of_affine_psi {x y A B : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hpsi : ∀ t : ℝ, 0 ≤ t → A * t + B ≤ Chebyshev.psi t) :
    A * x * (1 - Real.exp (-y / x)) + B ≤ exponentialMangoldtSum x y := by
  have he := mul_le_mul_of_nonneg_left (hpsi y hy) (Real.exp_pos (-y / x)).le
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-t / x)) :=
    Real.continuous_exp.comp (continuous_id.neg.div_const x)
  have hfi :
    MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-t / x) * Chebyshev.psi t) (Set.Ioc 0 y) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (a := (0 : ℝ)) (b := y)
        (by norm_num only) hc.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hgc : Continuous (fun t : ℝ ↦ Real.exp (-t / x) * (A * t + B)) :=
    hc.mul ((continuous_const.mul continuous_id).add continuous_const)
  have hi :=
    MeasureTheory.setIntegral_mono_on (hgc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) hfi
      measurableSet_Ioc
      (fun t ht ↦ mul_le_mul_of_nonneg_left (hpsi t ht.1.le) (Real.exp_pos (-t / x)).le)
  have hi' := mul_le_mul_of_nonneg_left hi (div_nonneg (by norm_num only : (0 : ℝ) ≤ 1) hx.le)
  rw [exponential_affine_setIntegral x A B hx.ne' hy] at hi'
  have ha :
    Real.exp (-y / x) * (A * y + B) +
        (1 / x) * (x * (A * x + B) - x * (A * (y + x) + B) * Real.exp (-y / x)) =
      A * x * (1 - Real.exp (-y / x)) + B := by
    field_simp [hx.ne']
    ring
  have hid := exponentialMangoldtSum_eq_psi_integral x hy
  linarith only [he, hi', ha, hid]

/-- A global linear-minus-square-root lower bound for psi yields a finite
exponential lower bound with square-root and constant errors. Use the tangent
at the smoothing scale before applying the affine Abel theorem. -/
theorem exponentialMangoldtSum_lower_of_sqrt_psi {a b c x y : ℝ} (hb : 0 ≤ b) (hx : 0 < x)
    (hy : 0 ≤ y) (hpsi : ∀ t : ℝ, 0 ≤ t → a * t - b * Real.sqrt t - c ≤ Chebyshev.psi t) :
    a * x * (1 - Real.exp (-y / x)) - b * Real.sqrt x - c ≤ exponentialMangoldtSum x y := by
  have hs := Real.sqrt_pos.mpr hx
  have hp (t : ℝ) (ht : 0 ≤ t) :
    (a - b / (2 * Real.sqrt x)) * t + (-b * Real.sqrt x / 2 - c) ≤ Chebyshev.psi t := by
    have h := mul_le_mul_of_nonneg_left (sqrt_le_reference_tangent ht hx) hb
    have he :
      (a - b / (2 * Real.sqrt x)) * t + (-b * Real.sqrt x / 2 - c) =
        a * t - b * ((t + x) / (2 * Real.sqrt x)) - c := by
      field_simp [hs.ne']
      linear_combination -b * (Real.sq_sqrt hx.le)
    rw [he]
    linarith only [h, hpsi t ht]
  have h := exponentialMangoldtSum_lower_of_affine_psi hx hy hp
  have he :
    (a - b / (2 * Real.sqrt x)) * x * (1 - Real.exp (-y / x)) + (-b * Real.sqrt x / 2 - c) =
      a * x * (1 - Real.exp (-y / x)) - b * Real.sqrt x - c +
        b * Real.sqrt x / 2 * Real.exp (-y / x) := by
    field_simp [hs.ne']
    linear_combination b * (1 - Real.exp (-(y / x))) * (Real.sq_sqrt hx.le)
  rw [he] at h
  have hn :=
    mul_nonneg (div_nonneg (mul_nonneg hb hs.le) (by norm_num only : (0 : ℝ) ≤ 2))
      (Real.exp_pos (-y / x)).le
  linarith only [h, hn]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
