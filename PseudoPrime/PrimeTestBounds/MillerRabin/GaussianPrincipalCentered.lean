/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalWeightDeriv
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianEulerPolyAbel
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.Linarith

/-! # Endpoint limits of the centered Gaussian principal weight -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected log-polynomial weight tends to zero at the left endpoint
when its power is positive. Use inversion and polynomial decay at infinity. -/
public theorem reflected_log_weight_tendsto_zero (B : Polynomial ℝ) {d : ℝ} (hd : 0 < d) (b : ℝ) :
    Filter.Tendsto (fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  have h :=
    (euler_poly_tendsto (B.comp (Polynomial.X + Polynomial.C b)) hd).comp tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with u hu
  have hp : 0 < u := hu
  simp only [Function.comp_apply, Real.inv_rpow hp.le, Real.rpow_neg hp.le, inv_inv,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Real.log_inv,
    sub_eq_add_neg, add_comm b]

/-- The lower endpoint term `u W'(u)` of the centered principal weight tends to zero. -/
public theorem reflected_log_boundary_zero (B : Polynomial ℝ) {d : ℝ} (hd : 0 < d) (b : ℝ) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    Filter.Tendsto (fun u ↦ u * deriv W u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro W
  apply (reflected_log_weight_tendsto_zero (Polynomial.C d * B - B.derivative) hd b).congr'
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))] with u hu
  have hp : 0 < u := hu
  rw [show deriv W u = _ from (reflected_log_weight_deriv B d b hp).deriv, ← mul_assoc, mul_comm u,
    Real.rpow_sub_one hp.ne', div_mul_cancel₀ _ hp.ne']

/-- Integrating the logarithmic derivative from zero leaves only the
value of the first logarithmic derivative at the positive endpoint. -/
public theorem reflected_principal_integral_zero (B : Polynomial ℝ) {d b v : ℝ} (hd : 0 < d)
    (hv : 0 < v) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv W u
    IntervalIntegrable (deriv F) MeasureTheory.volume 0 v →
      (∫ u in (0 : ℝ)..v, deriv F u) = F v := by
  intro W F hi
  have h (u : ℝ) (hu : 0 < u) : HasDerivAt F (deriv F u) u :=
    (reflected_log_weight_second B d b hu).differentiableAt.hasDerivAt
  exact
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hv (fun u hu ↦ h u hu.1) hi
          (reflected_log_boundary_zero B hd b) (h v hv).continuousAt.continuousWithinAt).trans
      (sub_zero _)

/-- Centering cancels constant terms in the principal Abel functional.
The derivative of the boundary function is integrated on each side of one. -/
private theorem reflected_principal_cancel_of_integrable (B : Polynomial ℝ) {d b : ℝ} (hd : 0 < d)
    (hb : 0 < b) (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) (F : ℝ → ℝ)
    (hF : F = fun u ↦ u * deriv (fun v ↦ v ^ d * B.eval (b - Real.log v)) u)
    (hint₁ : IntervalIntegrable (deriv F) MeasureTheory.volume 0 1)
    (hint₂ : IntervalIntegrable (deriv F) MeasureTheory.volume 1 (Real.exp b)) :
    3 * (∫ u in (0 : ℝ)..1, deriv F u) - (∫ u in (1 : ℝ)..Real.exp b, deriv F u) - 4 * F 1 = 0 := by
  subst F
  let W := fun v : ℝ ↦ v ^ d * B.eval (b - Real.log v)
  let F := fun u : ℝ ↦ u * deriv W u
  have hder (u : ℝ) (hu : 0 < u) : HasDerivAt F (deriv F u) u :=
    (reflected_log_weight_second B d b hu).differentiableAt.hasDerivAt
  have h₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one (fun u hu ↦ hder u hu.1)
      hint₁ (reflected_log_boundary_zero B hd b)
      ((hder 1 zero_lt_one).continuousAt.continuousWithinAt)
  have h₂ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (Real.one_le_exp_iff.mpr hb.le)
      (fun u hu ↦ (hder u (zero_lt_one.trans_le hu.1)).continuousAt.continuousWithinAt)
      (fun u hu ↦ hder u (zero_lt_one.trans hu.1)) hint₂
  have hright : F (Real.exp b) = 0 := by
    simp only [F, W, reflected_log_weight_endpoint B d b hB hB', mul_zero]
  change 3 * (∫ u in (0 : ℝ)..1, deriv F u) - (∫ u in (1 : ℝ)..Real.exp b, deriv F u) - 4 * F 1 = 0
  linarith only [h₁, h₂, hright]

/-- Inversion maps the tail above one to the interval from zero to one. -/
private theorem inv_image_above_one : (fun x : ℝ ↦ x⁻¹) '' Set.Ioi 1 = Set.Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx₀ : 0 < x := zero_lt_one.trans hx
    exact ⟨inv_pos.mpr hx₀, (inv_lt_one₀ hx₀).mpr hx⟩
  · intro hu
    exact ⟨u⁻¹, (one_lt_inv₀ hu.1).mpr hu.2, inv_inv u⟩

/-- The principal Abel kernel is integrable down to zero at every positive decay rate. -/
private theorem reflected_deriv_integrable_low (D : Polynomial ℝ) {d : ℝ} (hd : 0 < d) (b : ℝ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (d - 1) * D.eval (b - Real.log u))
      (Set.Ioo 0 1) := by
  let g := fun u : ℝ ↦ u ^ (d - 1) * D.eval (b - Real.log u)
  have h :=
    MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun x : ℝ ↦ x⁻¹) (f' :=
      fun x ↦ -(x ^ 2)⁻¹) (measurableSet_Ioi (a := (1 : ℝ)))
      (fun x hx ↦ (hasDerivAt_inv (zero_lt_one.trans hx).ne').hasDerivWithinAt)
      (fun _ _ _ _ h ↦ inv_injective h) g
  rw [inv_image_above_one] at h
  apply h.mpr
  have hi := euler_poly_integrable (D.comp (Polynomial.X + Polynomial.C b)) le_rfl hd
  refine hi.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  have hp : 0 < x := zero_lt_one.trans hx
  simp only [g, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    add_comm b, Real.log_inv, sub_neg_eq_add, smul_eq_mul, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg x)), Real.inv_rpow hp.le]
  rw [← mul_assoc, ← Real.rpow_two, ← Real.rpow_neg hp.le, ← Real.rpow_neg hp.le, ←
    Real.rpow_add hp]
  congr 2
  ring

/-- The differentiated boundary weight is integrable on both pieces of the principal functional. -/
public theorem reflected_principal_integrable (B : Polynomial ℝ) {d b : ℝ} (hd : 0 < d)
    (hb : 0 < b) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    IntervalIntegrable (deriv F) MeasureTheory.volume 0 1 ∧
      IntervalIntegrable (deriv F) MeasureTheory.volume 1 (Real.exp b) := by
  intro W F
  let D := Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
  have he (u : ℝ) (hu : 0 < u) : deriv F u = u ^ (d - 1) * D.eval (b - Real.log u) :=
    (reflected_log_weight_second B d b hu).deriv
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact
      (reflected_deriv_integrable_low D hd b).congr_fun (fun u hu ↦ (he u hu.1).symm)
        measurableSet_Ioo
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (Real.one_le_exp_iff.mpr hb.le)]
    intro u hu
    have hu₀ := zero_lt_one.trans_le hu.1
    have hc :=
      (Real.continuousAt_rpow_const u (d - 1) (Or.inl hu₀.ne')).mul
        (D.continuous.continuousAt.comp
          ((continuousAt_const (y := b)).sub (Real.continuousAt_log hu₀.ne')))
    exact hc.continuousWithinAt.congr (fun v hv ↦ he v (zero_lt_one.trans_le hv.1)) (he u hu₀)

/-- The constant contribution to the centered principal functional in H21 is zero.
The profile and its first derivative vanish at the right endpoint. -/
public theorem reflected_principal_cancel (B : Polynomial ℝ) {d b : ℝ} (hd : 0 < d) (hb : 0 < b)
    (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    3 * (∫ u in (0 : ℝ)..1, deriv F u) - (∫ u in (1 : ℝ)..Real.exp b, deriv F u) - 4 * F 1 = 0 := by
  have h := reflected_principal_integrable B hd hb
  exact reflected_principal_cancel_of_integrable B hd hb hB hB' _ rfl h.1 h.2

end PseudoPrime.PrimeTestBounds.MillerRabin
