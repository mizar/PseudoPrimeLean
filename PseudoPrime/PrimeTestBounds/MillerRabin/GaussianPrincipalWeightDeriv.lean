/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring

/-! # Two derivatives of the reflected Gaussian polynomial weight -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a reflected log-polynomial, multiplication of its derivative by `u`
corresponds to the polynomial operator `B ↦ dB - B'`. -/
public theorem reflected_log_weight_deriv (B : Polynomial ℝ) (d b : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u ↦ u ^ d * B.eval (b - Real.log u))
      (t ^ (d - 1) * (Polynomial.C d * B - B.derivative).eval (b - Real.log t)) t := by
  have hlog := (hasDerivAt_const t b).sub (Real.hasDerivAt_log ht.ne')
  have h :=
    (Real.hasDerivAt_rpow_const (p := d) (Or.inl ht.ne')).mul
      ((B.hasDerivAt (b - Real.log t)).comp t hlog)
  refine h.congr_deriv ?_
  rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C]
  simp only [Function.comp_apply, Pi.sub_apply, zero_sub]
  ring

/-- The principal Abel kernel in H20 is the derivative of `u W'(u)` on the positive half-line. -/
public theorem reflected_log_weight_second (B : Polynomial ℝ) (d b : ℝ) {t : ℝ} (ht : 0 < t) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    HasDerivAt (fun u ↦ u * deriv W u) (t ^ (d - 1) * D.eval (b - Real.log t)) t := by
  intro W D
  let C := Polynomial.C d * B - B.derivative
  have he :
    (fun u : ℝ ↦ u * deriv W u) =ᶠ[nhds t] (fun u : ℝ ↦ u ^ d * C.eval (b - Real.log u)) := by
    filter_upwards [lt_mem_nhds ht] with u hu
    rw [show deriv W u = _ from (reflected_log_weight_deriv B d b hu).deriv, ← mul_assoc,
      mul_comm u, Real.rpow_sub_one hu.ne', div_mul_cancel₀ _ hu.ne']
  have hd := (reflected_log_weight_deriv C d b ht).congr_of_eventuallyEq he
  refine hd.congr_deriv ?_
  simp only [C, D, Polynomial.derivative_sub, Polynomial.derivative_C_mul, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- The derivative at the right endpoint vanishes when the profile and its first
derivative vanish at zero. This is the endpoint condition for H21. -/
public theorem reflected_log_weight_endpoint (B : Polynomial ℝ) (d b : ℝ) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0) :
    deriv (fun u ↦ u ^ d * B.eval (b - Real.log u)) (Real.exp b) = 0 := by
  rw [(reflected_log_weight_deriv B d b (Real.exp_pos b)).deriv, Real.log_exp, sub_self,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hB, hB', mul_zero, sub_zero,
    mul_zero]

/-- The log-polynomial Euler weight with positive log argument shift has
derivative given by the polynomial operator B' minus σB. -/
public theorem log_euler_weight_deriv (B : Polynomial ℝ) (σ z : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u ↦ u ^ (-σ) * B.eval (z + Real.log u))
      (t ^ (-σ - 1) * (B.derivative.eval (z + Real.log t) - σ * B.eval (z + Real.log t))) t := by
  have hlog := (hasDerivAt_const t z).add (Real.hasDerivAt_log ht.ne')
  have h :=
    (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl ht.ne')).mul
      ((B.hasDerivAt (z + Real.log t)).comp t hlog)
  refine h.congr_deriv ?_
  rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  simp only [Function.comp_apply, Pi.add_apply, zero_add]
  ring

/-- The absolute derivative of the Euler weight is bounded by the
weighted absolute values of B and B', as used in H29. -/
public theorem log_euler_weight_deriv_abs_le (B : Polynomial ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (z : ℝ) {t : ℝ}
    (ht : 0 < t) :
    |deriv (fun u ↦ u ^ (-σ) * B.eval (z + Real.log u)) t| ≤
      t ^ (-σ - 1) * (σ * |B.eval (z + Real.log t)| + |B.derivative.eval (z + Real.log t)|) := by
  rw [(log_euler_weight_deriv B σ z ht).deriv, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
  exact (abs_sub _ _).trans_eq (by rw [abs_mul, abs_of_nonneg hσ, add_comm])

/-- Multiplying by the linear Chebyshev envelope cancels the extra inverse
power in the derivative bound. -/
public theorem log_euler_weight_abel_le (B : Polynomial ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (z : ℝ) {t : ℝ}
    (ht : 0 < t) :
    2 * t * |deriv (fun u ↦ u ^ (-σ) * B.eval (z + Real.log u)) t| ≤
      2 * t ^ (-σ) * (σ * |B.eval (z + Real.log t)| + |B.derivative.eval (z + Real.log t)|) := by
  have h :=
    mul_le_mul_of_nonneg_left (log_euler_weight_deriv_abs_le B hσ z ht)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) ht.le)
  have ht' : t * t ^ (-σ - 1) = t ^ (-σ) := by
    rw [mul_comm, Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
  rw [← mul_assoc (2 * t), mul_assoc 2 t (t ^ (-σ - 1)), ht'] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
