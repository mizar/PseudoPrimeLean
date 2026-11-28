/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroSum
import Mathlib.Tactic.Ring

/-! # Cutoff-independent coefficients for the principal zero terms -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Scaling the argument by a positive cutoff extracts its complex power. -/
private theorem log_zero_term_scale (X u : ℝ) (hX : 0 ≤ X) (ρ : ℂ) :
    AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (X * u) ρ =
      (X : ℂ) ^ ρ * AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ := by
  by_cases h : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  · simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_left h,
      AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution, Complex.ofReal_mul,
      Complex.ofReal_mul_cpow hX]
    ring
  · simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_right h, mul_zero]

/-- The real integral of one scaled zero term is the real part of its coefficient
multiplied by the cutoff power. -/
private theorem principal_zero_integral_scale (Q : ℝ → ℝ) (hRH : RiemannHypothesis) {X a b : ℝ}
    (hX : 0 ≤ X) (hQ : IntervalIntegrable Q MeasureTheory.volume a b) (ρ : ℂ) :
    (∫ u in a..b, (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (X * u) ρ).re * Q u) =
      (((X : ℂ) ^ ρ) *
          ∫ u in a..b, Q u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ).re := by
  let f := fun u ↦ Q u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ
  have hf : IntervalIntegrable f MeasureTheory.volume a b :=
    hQ.smul_continuousOn (gaussian_log_term_continuous hRH ρ).continuousOn
  have hi : IntervalIntegrable (fun u ↦ (X : ℂ) ^ ρ * f u) MeasureTheory.volume a b :=
    hf.const_mul _
  rw [← intervalIntegral.integral_const_mul]
  have h := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ u in a..b, ((X : ℂ) ^ ρ * f u).re) = (∫ u in a..b, (X : ℂ) ^ ρ * f u).re at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u _
  change
    (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm (X * u) ρ).re * Q u =
      ((X : ℂ) ^ ρ * (Q u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ)).re
  rw [log_zero_term_scale X u hX ρ]
  rw [mul_smul_comm]
  change _ = Complex.reCLM (Q u • ((X : ℂ) ^ ρ * _))
  rw [Complex.reCLM.map_smul]
  exact mul_comm _ _

/-- The centered principal coefficient of one logarithmic zero, with its
multiplicity and inverse-square factor included and the cutoff power omitted. -/
@[expose]
public noncomputable def principalZeroCoeff (Q : ℝ → ℝ) (edge y : ℝ) (ρ : ℂ) : ℂ :=
  3 * (∫ u in (0 : ℝ)..1, Q u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ) -
    (∫ u in (1 : ℝ)..y, Q u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ) -
    (4 * (edge : ℂ)) * AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm 1 ρ

/-- The principal functional applied to one logarithmic zero has a single cutoff power. -/
private theorem principal_zero_coeff_scale (Q : ℝ → ℝ) (hRH : RiemannHypothesis) {X y edge : ℝ}
    (hX : 0 ≤ X) (hQ₁ : IntervalIntegrable Q MeasureTheory.volume 0 1)
    (hQ₂ : IntervalIntegrable Q MeasureTheory.volume 1 y) (ρ : ℂ) :
    principalErrorFunctional Q
        (fun t ↦ (AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) edge X y =
      (((X : ℂ) ^ ρ) * principalZeroCoeff Q edge y ρ).re := by
  simp only [principalErrorFunctional, principalZeroCoeff,
    principal_zero_integral_scale Q hRH hX hQ₁, principal_zero_integral_scale Q hRH hX hQ₂]
  have hx := log_zero_term_scale X 1 hX ρ
  rw [mul_one] at hx
  rw [hx, mul_sub, mul_sub, Complex.sub_re, Complex.sub_re]
  congr 1
  · congr 1
    rw [← mul_assoc, mul_comm ((X : ℂ) ^ ρ) 3, mul_assoc]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  · rw [← mul_assoc, mul_comm ((X : ℂ) ^ ρ), mul_assoc]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero]
    ring

/-- The high-kernel principal zero sum is a cutoff-power series with coefficients
given by the unscaled centered complex integrals. -/
public theorem high_principal_coeff_hasSum (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    HasSum (fun ρ : ℂ ↦ ((X : ℂ) ^ ρ * principalZeroCoeff (deriv F) (F 1) (Real.exp 5) ρ).re)
      (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5)) := by
  intro d W F
  have hb : (0 : ℝ) < 5 := by norm_num only
  have hi := reflected_principal_integrable K.realProfile (sub_pos.mpr (high_gaussian_pole_gt K)) hb
  exact
    (high_principal_zero_hasSum K hRH hX).congr_fun
      (fun ρ ↦ (principal_zero_coeff_scale (deriv F) hRH hX.le hi.1 hi.2 ρ).symm)

/-- On the critical line the cutoff power separates into a positive scale and a unit phase. -/
private theorem crit_cpow_phase {X : ℝ} (hX : 0 < X) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    (X : ℂ) ^ ρ = (Real.sqrt X : ℂ) * Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hX.ne'), ← Complex.ofReal_log hX.le,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX, Complex.ofReal_exp]
  have h : ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * Complex.I := by
    have hh := Complex.re_add_im ρ
    rw [hρ, Complex.ofReal_div, Complex.ofReal_one] at hh
    norm_num only [Complex.ofReal_ofNat] at hh
    exact hh.symm
  have he :
    (Real.log X : ℂ) * ρ =
      (Real.log X * (1 / 2 : ℝ) : ℝ) + (Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I := by
    conv_lhs => rw [h]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he, Complex.exp_add]

/-- After dividing by `sqrt X`, a principal zero term carries only its unit phase.
The coefficient vanishes away from the nontrivial zeta zero support. -/
private theorem principal_zero_normalized (Q : ℝ → ℝ) (edge y : ℝ) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 < X) (ρ : ℂ) :
    ((X : ℂ) ^ ρ * principalZeroCoeff Q edge y ρ).re / Real.sqrt X =
      (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
          principalZeroCoeff Q edge y ρ).re := by
  by_cases h : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  · have hz := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg h.1 h.2
    have hr := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hz
    rw [crit_cpow_phase hX hr, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mul_div_cancel_left₀ _ (Real.sqrt_pos.2 hX).ne']
  · simp only [principalZeroCoeff, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm,
      ite_eq_right h, smul_zero, intervalIntegral.integral_zero, mul_zero, sub_zero,
      Complex.zero_re, zero_div]

/-- Under RH, normalize an integrable centered zero functional by the square root
of the cutoff to obtain the series of unit phases times unscaled coefficients. -/
public theorem principal_phase_hasSum (Q : ℝ → ℝ) (edge : ℝ) (hRH : RiemannHypothesis) {X y : ℝ}
    (hX : 0 < X) (hy : 1 ≤ y) (h₁ : IntervalIntegrable Q MeasureTheory.volume 0 1)
    (h₂ : IntervalIntegrable Q MeasureTheory.volume 1 y) :
    HasSum
      (fun ρ : ℂ ↦
        (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
            principalZeroCoeff Q edge y ρ).re)
      (principalErrorFunctional Q gaussianLogZetaZeroSum edge X y / Real.sqrt X) := by
  have h := (principal_zero_hasSum Q edge hRH hX hy h₁ h₂).div_const (Real.sqrt X)
  refine h.congr_fun (fun ρ ↦ ?_)
  rw [principal_zero_coeff_scale Q hRH hX.le h₁ h₂ ρ]
  exact (principal_zero_normalized Q edge y hRH hX ρ).symm

/-- On RH, the normalized high principal zero sum is the series of unit phases
times cutoff-independent coefficients. -/
public theorem high_principal_phase_hasSum (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    HasSum
      (fun ρ : ℂ ↦
        (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
            principalZeroCoeff (deriv F) (F 1) (Real.exp 5) ρ).re)
      (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
        Real.sqrt X) := by
  intro d W F
  have hb : (0 : ℝ) < 5 := by norm_num only
  have hi := reflected_principal_integrable K.realProfile (sub_pos.mpr (high_gaussian_pole_gt K)) hb
  exact principal_phase_hasSum (deriv F) (F 1) hRH hX (Real.one_le_exp hb.le) hi.1 hi.2

end PseudoPrime.PrimeTestBounds.MillerRabin
