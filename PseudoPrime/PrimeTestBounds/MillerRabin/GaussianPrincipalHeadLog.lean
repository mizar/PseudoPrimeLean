/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalKernelMoment
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.Ring

/-! # Reflected logarithmic coordinate for the principal head -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Reflection after taking logs sends the upper-support interval onto `(0,b)`. -/
private theorem head_log_image (b : ℝ) :
    (fun u : ℝ ↦ b - Real.log u) '' Set.Ioo 1 (Real.exp b) = Set.Ioo 0 b := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu₀ := zero_lt_one.trans hu.1
    have h := Real.log_lt_log hu₀ hu.2
    rw [Real.log_exp] at h
    exact ⟨sub_pos.mpr h, sub_lt_self _ (Real.log_pos hu.1)⟩
  · intro ht
    refine ⟨Real.exp (b - t), ⟨?_, Real.exp_lt_exp.mpr (sub_lt_self _ ht.1)⟩, ?_⟩
    · rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (sub_pos.mpr ht.2)
    · change b - Real.log (Real.exp (b - t)) = t
      rw [Real.log_exp, sub_sub_cancel]

/-- The upper interval moment is an ordinary complex exponential moment on `[0,b]`. -/
public theorem principal_head_log_coord (B : Polynomial ℝ) (s : ℂ) {b : ℝ} (hb : 0 < b) :
    (∫ u in (1 : ℝ)..Real.exp b, (u : ℂ) ^ (s - 1) * Complex.ofReal (B.eval (b - Real.log u))) =
      Complex.exp ((b : ℂ) * s) *
        ∫ v in (0 : ℝ)..b, Complex.exp (-(v : ℂ) * s) * Complex.ofReal (B.eval v) := by
  let g := fun v : ℝ ↦ Complex.exp (((b - v : ℝ) : ℂ) * s) * Complex.ofReal (B.eval v)
  have hd (u : ℝ) (hu : u ∈ Set.Ioo 1 (Real.exp b)) :
    HasDerivWithinAt (fun v : ℝ ↦ b - Real.log v) (-u⁻¹) (Set.Ioo 1 (Real.exp b)) u := by
    change HasDerivWithinAt ((fun _ : ℝ ↦ b) - Real.log) (-u⁻¹) _ u
    simpa only [zero_sub] using
      ((hasDerivAt_const u b).sub
          (Real.hasDerivAt_log (zero_lt_one.trans hu.1).ne')).hasDerivWithinAt
  have hi : Set.InjOn (fun u : ℝ ↦ b - Real.log u) (Set.Ioo 1 (Real.exp b)) := fun _ hu _ hv he ↦
    Real.log_injOn_pos (zero_lt_one.trans hu.1) (zero_lt_one.trans hv.1) (sub_right_injective he)
  have hj := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hi g
  rw [head_log_image b] at hj
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le hb.le,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (Real.one_le_exp_iff.mpr hb.le),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    _ = ∫ u in Set.Ioo (1 : ℝ) (Real.exp b), |-u⁻¹| • g (b - Real.log u) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      have hp := zero_lt_one.trans hu.1
      simp only [g, sub_sub_cancel, abs_neg, abs_of_nonneg (inv_pos.mpr hp).le, Complex.real_smul,
        Complex.ofReal_inv]
      rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hp.ne'), Complex.cpow_one,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne') s, ←
        Complex.ofReal_log hp.le, div_eq_mul_inv, ← mul_assoc, mul_comm (Complex.exp _)]
    _ = ∫ v in Set.Ioo 0 b, g v := hj.symm
    _ = _ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro v _
      dsimp only [g]
      rw [Complex.ofReal_sub, sub_mul, sub_eq_add_neg, Complex.exp_add, neg_mul, mul_assoc]

/-- The physical scaling shifts the upper interval's exponential prefactor by the pole. -/
public theorem scaled_principal_head_log (B : Polynomial ℝ) (a z : ℂ) {b : ℝ} (hb : 0 < b) :
    Complex.exp (-(b : ℂ) * a) *
        (∫ u in (1 : ℝ)..Real.exp b,
          (u : ℂ) ^ (z + a - 1) * Complex.ofReal (B.eval (b - Real.log u))) =
      Complex.exp ((b : ℂ) * z) *
        ∫ v in (0 : ℝ)..b, Complex.exp (-(v : ℂ) * (z + a)) * Complex.ofReal (B.eval v) := by
  rw [principal_head_log_coord B (z + a) hb, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The H25 coefficient in the logarithmic coordinate used to bound its variation.
The head is an exponential moment over the fixed interval from zero to five. -/
public theorem high_principal_coeff_log (K : HighGaussianKernel) {ρ : ℂ}
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let z := ρ - (1 / 2 : ℂ)
    let s := z + (K.pole : ℂ)
    let E := Complex.exp (-(5 * (K.pole : ℂ)))
    let k :=
      (K.normalization : ℂ) * Complex.exp (5 * z) * (K.polynomial.eval₂ (Rat.castHom ℂ) s) ^ 2 /
        s ^ (2 * K.degree + 4)
    let head :=
      Complex.exp (5 * z) *
        ∫ v in (0 : ℝ)..5, Complex.exp (-(v : ℂ) * s) * Complex.ofReal (K.realProfile.eval v)
    E * highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        (-3 * k + 4 * head + 4 * (E * (K.realProfile.eval 5 : ℝ)) / ρ) := by
  have h := high_principal_coeff_head K hz hρ
  dsimp only at h ⊢
  rw [← neg_mul] at h
  have hh :=
    scaled_principal_head_log K.realProfile (K.pole : ℂ) (ρ - 1 / 2)
      (by norm_num only : (0 : ℝ) < 5)
  simp only [Complex.ofReal_ofNat] at hh
  rw [hh] at h
  simpa only [neg_mul] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
