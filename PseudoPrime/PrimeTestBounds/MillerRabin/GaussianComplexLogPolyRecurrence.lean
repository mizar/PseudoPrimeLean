/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianComplexLogPoly
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalCentered
import Mathlib.Tactic.Ring

/-! # Integration by parts for complex logarithmic polynomial moments -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected complex Mellin primitive vanishes at the left endpoint. -/
private theorem complex_poly_boundary_zero (P : Polynomial ℝ) (b : ℝ) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun u : ℝ ↦ (u : ℂ) ^ s * Complex.ofReal (P.eval (b - Real.log u)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h := (reflected_log_weight_tendsto_zero P hs b).norm
  rw [norm_zero] at h
  apply squeeze_zero_norm' ?_ h
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with u hu
  have hp : 0 < u := hu
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.norm_real, norm_mul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _)]

/-- Differentiating the primitive gives the Mellin power times the reflected derivative. -/
private theorem complex_poly_primitive_deriv (P : Polynomial ℝ) (b : ℝ) {s : ℂ} (hs : 0 < s.re)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ s * Complex.ofReal (P.eval (b - Real.log t)))
      ((u : ℂ) ^ (s - 1) *
        (s * Complex.ofReal (P.eval (b - Real.log u)) -
          Complex.ofReal (P.derivative.eval (b - Real.log u))))
      u := by
  have hne : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    exact (lt_irrefl _ hs)
  have hlog := (hasDerivAt_const u b).sub (Real.hasDerivAt_log hu.ne')
  have hP := (P.hasDerivAt (b - Real.log u)).comp u hlog
  have hPC := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hP
  have hc := (hasDerivAt_ofReal_cpow_const hu.ne' hne).mul hPC
  refine hc.congr_deriv ?_
  simp only [Function.comp_apply, Pi.sub_apply, zero_sub, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_inv, Complex.ofRealCLM_apply]
  have hp : (u : ℂ) ^ s = (u : ℂ) ^ (s - 1) * u := by
    calc
      _ = (u : ℂ) ^ (s - 1 + 1) := by rw [sub_add_cancel]
      _ = _ := by rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne'), Complex.cpow_one]
  rw [hp]
  field_simp [Complex.ofReal_ne_zero.mpr hu.ne']
  ring

/-- The complex reflected Mellin moment satisfies the polynomial integration-by-parts recurrence. -/
public theorem complex_log_poly_moment_step (P : Polynomial ℝ) (b : ℝ) {s : ℂ} (hs : 0 < s.re) :
    s * complexLogPolyMoment P b s - complexLogPolyMoment P.derivative b s =
      Complex.ofReal (P.eval b) := by
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (P.eval (b - Real.log u))
  let g := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (P.derivative.eval (b - Real.log u))
  have hf := complex_log_poly_cutoff P b hs zero_lt_one
  have hg := complex_log_poly_cutoff P.derivative b hs zero_lt_one
  have hd (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ s * Complex.ofReal (P.eval (b - Real.log t))) (s * f u - g u)
      u :=
    (complex_poly_primitive_deriv P b hs hu).congr_deriv
      (by
        dsimp only [f, g]; ring)
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one (fun u hu ↦ hd u hu.1)
      ((hf.1.const_mul s).sub hg.1) (complex_poly_boundary_zero P b hs)
      ((hd 1 zero_lt_one).continuousAt.continuousWithinAt)
  rw [intervalIntegral.integral_sub (hf.1.const_mul s) hg.1, intervalIntegral.integral_const_mul,
    hf.2, hg.2] at h
  simpa only [Complex.ofReal_one, Complex.one_cpow, Real.log_one, sub_zero, one_mul] using h

/-- Scaling and subtracting polynomials commute with the complex Mellin moment. -/
public theorem complex_log_poly_moment_sub (P Q : Polynomial ℝ) (a b : ℝ) {s : ℂ} (hs : 0 < s.re) :
    complexLogPolyMoment (Polynomial.C a * P - Q) b s =
      (a : ℂ) * complexLogPolyMoment P b s - complexLogPolyMoment Q b s := by
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (P.eval (b - Real.log u))
  let g := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (Q.eval (b - Real.log u))
  have hf := complex_log_poly_cutoff P b hs zero_lt_one
  have hg := complex_log_poly_cutoff Q b hs zero_lt_one
  have hk := complex_log_poly_cutoff (Polynomial.C a * P - Q) b hs zero_lt_one
  have he :
    (∫ u in (0 : ℝ)..1,
        (u : ℂ) ^ (s - 1) * Complex.ofReal ((Polynomial.C a * P - Q).eval (b - Real.log u))) =
      ∫ u in (0 : ℝ)..1, (a : ℂ) * f u - g u := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [f, g, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Complex.ofReal_sub, Complex.ofReal_mul]
    ring
  rw [intervalIntegral.integral_sub (hf.1.const_mul _) hg.1, intervalIntegral.integral_const_mul,
    hf.2, hg.2, hk.2] at he
  simpa only [Complex.ofReal_one, Complex.one_cpow, Real.log_one, sub_zero, one_mul] using he

end PseudoPrime.PrimeTestBounds.MillerRabin
