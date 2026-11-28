/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianComplexLogPoly
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroPhase
import Mathlib.Tactic.Ring

/-! # Finite evaluation of the centered principal zero coefficient -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a nontrivial zero, the centered coefficient is a finite combination of
two exactly evaluated complex log-polynomial moments and the middle endpoint. -/
public theorem principal_zero_coeff_finite (B : Polynomial ℝ) {d b : ℝ} (hd : 0 < d) (hb : 0 < b)
    {ρ : ℂ} (hρ : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let s := (d : ℂ) + ρ
    principalZeroCoeff (deriv F) (F 1) (Real.exp b) ρ =
      (-(AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) / ρ ^ 2) *
        (4 * complexLogPolyMoment D b s - ((Real.exp b : ℝ) : ℂ) ^ s * complexLogPolyMoment D 0 s -
          4 * (F 1 : ℂ)) := by
  intro W F D s
  let c := -(AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) / ρ ^ 2
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (D.eval (b - Real.log u))
  have hs : 0 < s.re := by
    change 0 < ((d : ℂ) + ρ).re
    rw [Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg hd hρ.2
  have he (u : ℝ) (hu : 0 < u) :
    deriv F u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ = c * f u := by
    rw [show deriv F u = _ from (reflected_log_weight_second B d b hu).deriv,
      AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_left hρ]
    simp only [AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_cpow hu.le, Complex.ofReal_sub, Complex.ofReal_one, f, c,
      s]
    rw [show (d : ℂ) + ρ - 1 = ((d : ℂ) - 1) + ρ by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne')]
    ring
  have hi₁ := complex_log_poly_cutoff D b hs zero_lt_one
  have hi₂ := complex_log_poly_cutoff D b hs (Real.exp_pos b)
  have hle := Real.one_le_exp_iff.mpr hb.le
  have hi₃ : IntervalIntegrable f MeasureTheory.volume 1 (Real.exp b) := by
    apply hi₂.1.mono_set
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le (Real.exp_pos b).le]
    exact Set.Icc_subset_Icc zero_le_one le_rfl
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi₁.1 hi₃
  have ha :
    (∫ u in (0 : ℝ)..1, deriv F u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ) =
      c * ∫ u in (0 : ℝ)..1, f u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_Ioo_of_le zero_le_one (fun u hu ↦ he u hu.1)
  have hb' :
    (∫ u in (1 : ℝ)..Real.exp b,
        deriv F u • AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm u ρ) =
      c * ∫ u in (1 : ℝ)..Real.exp b, f u := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_Ioo_of_le hle (fun u hu ↦ he u (zero_lt_one.trans hu.1))
  have h₁ : (∫ u in (0 : ℝ)..1, f u) = complexLogPolyMoment D b s := by
    simpa only [Complex.ofReal_one, Complex.one_cpow, Real.log_one, sub_zero, one_mul] using hi₁.2
  have h₂ :
    (∫ u in (0 : ℝ)..Real.exp b, f u) =
      ((Real.exp b : ℝ) : ℂ) ^ s * complexLogPolyMoment D 0 s := by
    simpa only [Real.log_exp, sub_self] using hi₂.2
  have h₃ :
    (∫ u in (1 : ℝ)..Real.exp b, f u) =
      ((Real.exp b : ℝ) : ℂ) ^ s * complexLogPolyMoment D 0 s - complexLogPolyMoment D b s := by
    rw [← h₁, ← h₂, ← hsum, add_sub_cancel_left]
  rw [principalZeroCoeff, ha, hb', h₁, h₃]
  simp only [AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, ite_eq_left hρ,
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution, Complex.ofReal_one,
    Complex.one_cpow, mul_one]
  change _ = c * _
  dsimp only [c]
  ring

/-- The centered coefficient of a high-kernel zero, evaluated by two finite polynomial moments. -/
@[expose]
public noncomputable def highPrincipalFiniteCoeff (K : HighGaussianKernel) (ρ : ℂ) : ℂ :=
  if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re then
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let D :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let s := (d : ℂ) + ρ
    let edge := (Polynomial.C d * B - B.derivative).eval 5
    (-(AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) / ρ ^ 2) *
      (4 * complexLogPolyMoment D 5 s - (Real.exp 5 : ℂ) ^ s * complexLogPolyMoment D 0 s -
        4 * (edge : ℂ))
  else 0

/-- The finite high-kernel coefficient agrees with the centered functional at each zero. -/
public theorem high_principal_finite_coeff_eq (K : HighGaussianKernel) (ρ : ℂ) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    principalZeroCoeff (deriv F) (F 1) (Real.exp 5) ρ = highPrincipalFiniteCoeff K ρ := by
  intro d W F
  by_cases hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  · have h :=
      principal_zero_coeff_finite K.realProfile (sub_pos.mpr (high_gaussian_pole_gt K))
        (by norm_num only : (0 : ℝ) < 5) hz
    have hF : F 1 = (Polynomial.C d * K.realProfile - K.realProfile.derivative).eval 5 := by
      change 1 * deriv W 1 = _
      rw [(reflected_log_weight_deriv K.realProfile d 5 zero_lt_one).deriv, Real.log_one, sub_zero,
        Real.one_rpow, one_mul, one_mul]
    change principalZeroCoeff (deriv F) (F 1) (Real.exp 5) ρ = _ at h
    dsimp only [F, W, d] at hF
    rw [h, highPrincipalFiniteCoeff, ite_eq_left hz]
    dsimp only
    rw [hF]
  · simp only [highPrincipalFiniteCoeff, ite_eq_right hz, principalZeroCoeff,
      AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, smul_zero,
      intervalIntegral.integral_zero, mul_zero, sub_zero]

/-- The normalized principal zero sum is a series of phases times finite evaluated coefficients. -/
public theorem high_principal_finite_hasSum (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    HasSum
      (fun ρ : ℂ ↦
        (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) * highPrincipalFiniteCoeff K ρ).re)
      (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
        Real.sqrt X) := by
  intro d W F
  refine (high_principal_phase_hasSum K hRH hX).congr_fun (fun ρ ↦ ?_)
  rw [← high_principal_finite_coeff_eq K ρ]

end PseudoPrime.PrimeTestBounds.MillerRabin
