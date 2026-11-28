/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleCompensationAbel

/-! # Logarithmic derivatives for the middle Gaussian Euler weight -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rescale the physical weight to a function of the ratio to the cutoff. -/
public theorem middle_comp_weight_rescale (C : ℝ → ℝ) {s b a t : ℝ} (ht : 0 < t) :
    middleCompWeight C (Real.exp s) b a t =
      Real.exp (-s / 2) *
        (Real.exp (-a * b) * (t / Real.exp s) ^ (a - 1 / 2) *
          C (b - Real.log (t / Real.exp s))) := by
  have hu : 0 < t / Real.exp s := div_pos ht (Real.exp_pos _)
  simp only [middleCompWeight, Real.rpow_def_of_pos ht, Real.rpow_def_of_pos hu, ← Real.exp_add,
    ← mul_assoc]
  rw [Real.log_div ht.ne' (Real.exp_pos _).ne', Real.log_exp]
  congr 2
  ring

/-- Differentiate a power times a polynomial in the reversed logarithm. -/
public theorem middle_log_poly_deriv (P : Polynomial ℝ) (b d : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun x : ℝ ↦ x ^ d * P.eval (b - Real.log x))
      (u ^ (d - 1) * (Polynomial.C d * P - P.derivative).eval (b - Real.log u)) u := by
  have hlog := (hasDerivAt_const u b).sub (Real.hasDerivAt_log hu.ne')
  have h :=
    (Real.hasDerivAt_rpow_const (p := d) (Or.inl hu.ne')).mul
      ((P.hasDerivAt (b - Real.log u)).comp u hlog)
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    zero_sub, Pi.sub_apply]
  rw [Real.rpow_sub_one hu.ne', div_eq_mul_inv]
  ring

/-- Apply the same derivative rule to obtain the second derivative. -/
public theorem middle_log_poly_second (P : Polynomial ℝ) (b d : ℝ) {u : ℝ} (hu : 0 < u) :
    let Q := Polynomial.C d * P - P.derivative
    HasDerivAt (deriv (fun x : ℝ ↦ x ^ d * P.eval (b - Real.log x)))
      (u ^ (d - 2) * (Polynomial.C (d - 1) * Q - Q.derivative).eval (b - Real.log u)) u := by
  intro Q
  have h := middle_log_poly_deriv Q b (d - 1) hu
  have he :
    (fun x : ℝ ↦ x ^ (d - 1) * Q.eval (b - Real.log x)) =ᶠ[nhds u]
      deriv (fun x : ℝ ↦ x ^ d * P.eval (b - Real.log x)) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    exact (middle_log_poly_deriv P b d hx).deriv.symm
  have hd : d - 1 - 1 = d - 2 := by ring
  simpa only [hd] using h.congr_of_eventuallyEq he.symm

end PseudoPrime.PrimeTestBounds.MillerRabin
