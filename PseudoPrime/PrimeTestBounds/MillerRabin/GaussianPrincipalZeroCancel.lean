/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianComplexLogPolyRecurrence
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroCoeff
import Mathlib.Tactic.LinearCombination

/-! # Cancellation in the high principal zero coefficient -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Applying the reflected derivative operator subtracts `ρ` times the moment
and adds the value of the polynomial at the shift. -/
private theorem complex_moment_reflect (P : Polynomial ℝ) (d b : ℝ) (ρ : ℂ)
    (hs : 0 < ((d : ℂ) + ρ).re) :
    let s := (d : ℂ) + ρ
    complexLogPolyMoment (Polynomial.C d * P - P.derivative) b s =
      (P.eval b : ℝ) - ρ * complexLogPolyMoment P b s := by
  intro s
  rw [complex_log_poly_moment_sub P P.derivative d b hs]
  have h := complex_log_poly_moment_step P b hs
  dsimp only [s]
  linear_combination h

/-- Applying the reflected derivative twice gives the cancellation used in H25. -/
private theorem complex_moment_reflect_twice (P : Polynomial ℝ) (d b : ℝ) (ρ : ℂ)
    (hs : 0 < ((d : ℂ) + ρ).re) :
    let s := (d : ℂ) + ρ
    let C := Polynomial.C d * P - P.derivative
    let D :=
      Polynomial.C (d ^ 2) * P - Polynomial.C (2 * d) * P.derivative + P.derivative.derivative
    complexLogPolyMoment D b s =
      (C.eval b : ℝ) - ρ * (P.eval b : ℝ) + ρ ^ 2 * complexLogPolyMoment P b s := by
  intro s C D
  have he : D = Polynomial.C d * C - C.derivative := by
    simp only [C, D, Polynomial.derivative_sub, Polynomial.derivative_C_mul, Polynomial.C_mul,
      Polynomial.C_pow, Polynomial.C_ofNat]
    ring
  rw [he, complex_moment_reflect C d b ρ hs, complex_moment_reflect P d b ρ hs]
  ring

/-- Cancel the reflected derivatives in the finite principal zero coefficient
for any profile whose value and first derivative vanish at the support endpoint. -/
public theorem principal_zero_coeff_cancel (B : Polynomial ℝ) {d b : ℝ} (hd : 0 < d) (hb : 0 < b)
    (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) {ρ : ℂ} (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re)
    (hρ : ρ ≠ 0) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv W u
    let s := (d : ℂ) + ρ
    principalZeroCoeff (deriv F) (F 1) (Real.exp b) ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        ((Real.exp b : ℂ) ^ s * complexLogPolyMoment B 0 s - 4 * complexLogPolyMoment B b s +
          4 * (B.eval b : ℝ) / ρ) := by
  intro W F s
  have hs : 0 < ((d : ℂ) + ρ).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg hd hz.2
  have h0 : (Polynomial.C d * B - B.derivative).eval 0 = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hB, hB', mul_zero,
      sub_self]
  have h1 : F 1 = (Polynomial.C d * B - B.derivative).eval b := by
    change 1 * deriv W 1 = _
    rw [(reflected_log_weight_deriv B d b zero_lt_one).deriv, Real.log_one, sub_zero, Real.one_rpow,
      one_mul, one_mul]
  rw [principal_zero_coeff_finite B hd hb hz, complex_moment_reflect_twice B d b ρ hs,
    complex_moment_reflect_twice B d 0 ρ hs]
  simp only [hB, h0, Complex.ofReal_zero, mul_zero, sub_zero, zero_add]
  dsimp only [F, W] at h1
  rw [h1]
  dsimp only [s]
  field_simp (disch := exact hρ)
  ring

/-- The normalized centered contribution of a nontrivial zero, evaluated with
two moments of the original profile and its cutoff value. -/
@[expose]
public noncomputable def principalCancelledTerm (B : Polynomial ℝ) (d b X : ℝ) (ρ : ℂ) : ℝ :=
  if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re then
      let s := (d : ℂ) + ρ
      (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
        ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
          ((Real.exp b : ℂ) ^ s * complexLogPolyMoment B 0 s - 4 * complexLogPolyMoment B b s +
            4 * (B.eval b : ℝ) / ρ))).re
  else 0

/-- On the zero support, absorb the cutoff value into the first reflected
derivative moment. The resulting truncated moment has an extra inverse pole. -/
public theorem principal_cancelled_first (B : Polynomial ℝ) (d b X : ℝ) {ρ : ℂ}
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) (hρ : ρ ≠ 0) (hs : 0 < ((d : ℂ) + ρ).re) :
    let s := (d : ℂ) + ρ
    let C := Polynomial.C d * B - B.derivative
    principalCancelledTerm B d b X ρ =
      (Complex.exp ((Real.log X : ℂ) * (ρ.im : ℂ) * Complex.I) *
          ((AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
            ((Real.exp b : ℂ) ^ s * complexLogPolyMoment B 0 s +
              4 * (complexLogPolyMoment C b s / ρ)))).re := by
  intro s C
  rw [principalCancelledTerm, ite_eq_left hz]
  have h := complex_moment_reflect B d b ρ hs
  dsimp only [C, s] at h ⊢
  rw [h]
  congr 3
  field_simp (disch := exact hρ)
  ring

/-- For a profile vanishing to second order at zero, the centered principal
series sums the cancelled contributions. -/
public theorem principal_cancelled_hasSum (B : Polynomial ℝ) (hRH : RiemannHypothesis) {d b X : ℝ}
    (hd : 0 < d) (hb : 0 < b) (hX : 0 < X) (hB : B.eval 0 = 0) (hB' : B.derivative.eval 0 = 0) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u ↦ u * deriv W u
    HasSum (principalCancelledTerm B d b X)
      (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp b) /
        Real.sqrt X) := by
  intro W F
  have hi := reflected_principal_integrable B hd hb
  refine
    (principal_phase_hasSum (deriv F) (F 1) hRH hX (Real.one_le_exp hb.le) hi.1 hi.2).congr_fun
      (fun ρ ↦ ?_)
  by_cases hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  · have hn : ρ ≠ 0 := by
      intro h
      have he := hz.1
      rw [h, riemannZeta_zero] at he
      exact (by norm_num only : (-1 / 2 : ℂ) ≠ 0) he
    rw [principalCancelledTerm, ite_eq_left hz, principal_zero_coeff_cancel B hd hb hB hB' hz hn]
  · simp only [principalCancelledTerm, ite_eq_right hz, principalZeroCoeff,
      AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, smul_zero,
      intervalIntegral.integral_zero, mul_zero, sub_zero, Complex.zero_re]

/-- The high-kernel zero coefficient cancels its second-derivative moments.
The result uses the original profile moment at zero and five and the middle value. -/
public theorem high_principal_coeff_cancel (K : HighGaussianKernel) {ρ : ℂ}
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let s := (d : ℂ) + ρ
    highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        ((Real.exp 5 : ℂ) ^ s * complexLogPolyMoment B 0 s - 4 * complexLogPolyMoment B 5 s +
          4 * (B.eval 5 : ℝ) / ρ) := by
  intro d B s
  have hs : 0 < ((d : ℂ) + ρ).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr (high_gaussian_pole_gt K)) hz.2
  have hB := high_real_profile_at_zero K
  have hC : (Polynomial.C d * B - B.derivative).eval 0 = 0 := by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      show B.eval 0 = 0 from hB.1, show B.derivative.eval 0 = 0 from hB.2, mul_zero, sub_zero]
  rw [highPrincipalFiniteCoeff, ite_eq_left hz]
  dsimp only
  rw [complex_moment_reflect_twice B d 5 ρ hs, complex_moment_reflect_twice B d 0 ρ hs]
  simp only [show B.eval 0 = 0 from hB.1, hC, Complex.ofReal_zero, mul_zero, sub_zero, zero_add]
  dsimp only [s, B, d]
  field_simp [hρ]
  ring

/-- The centered coefficient in the form of H24 uses a first-derivative moment
at the middle endpoint and the full moment at the upper endpoint. -/
public theorem high_principal_coeff_first (K : HighGaussianKernel) {ρ : ℂ}
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let d := (K.pole : ℝ) - 1 / 2
    let B := K.realProfile
    let s := (d : ℂ) + ρ
    highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        ((Real.exp 5 : ℂ) ^ s * complexLogPolyMoment B 0 s +
          4 * complexLogPolyMoment (Polynomial.C d * B - B.derivative) 5 s / ρ) := by
  intro d B s
  have hs : 0 < ((d : ℂ) + ρ).re := by
    rw [Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr (high_gaussian_pole_gt K)) hz.2
  have h := complex_moment_reflect B d 5 ρ hs
  change
    complexLogPolyMoment (Polynomial.C d * B - B.derivative) 5 s =
      (B.eval 5 : ℝ) - ρ * complexLogPolyMoment B 5 s at h
  rw [h, high_principal_coeff_cancel K hz hρ]
  dsimp only [s, B, d]
  field_simp [hρ]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
