/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.InverseZeros
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FarLeftReflection
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorMultiplicityBridge
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroContribution

/-!
# Simple trivial zeros of primitive Dirichlet L-functions

The completed function is nonzero in the left half-plane. Its product with the
entire reciprocal archimedean factor therefore has the same simple trivial zeros.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The reciprocal gamma factor of any complex Dirichlet character is entire.
Even parity uses `Gammaℝ`; odd parity composes it with translation by one.
This makes analytic-order multiplication valid at the gamma poles. -/
theorem differentiable_inverse_gammaFactor {N : ℕ} (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (fun s : ℂ => (DirichletCharacter.gammaFactor χ s)⁻¹) := by
  rcases χ.even_or_odd with he | ho
  · have heq :
      (fun s : ℂ => (DirichletCharacter.gammaFactor χ s)⁻¹) = (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
      funext fun s => congrArg Inv.inv (he.gammaFactor_def s)
    rw [heq]
    exact Complex.differentiable_Gammaℝ_inv
  · have heq :
      (fun s : ℂ => (DirichletCharacter.gammaFactor χ s)⁻¹) =
        (fun s : ℂ => (Complex.Gammaℝ (s + 1))⁻¹) :=
      funext fun s => congrArg Inv.inv (ho.gammaFactor_def s)
    rw [heq]
    exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1)

/-- At a zero of the totalized gamma factor its reciprocal has analytic order one.
The parity formulas reduce the claim to the simple zeros of reciprocal `Gammaℝ`.
This order supplies the exact multiplicity of ordinary trivial zeros. -/
theorem analyticOrderAt_inverse_gammaFactor_of_zero {N : ℕ} {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) :
    analyticOrderAt (fun s : ℂ => (DirichletCharacter.gammaFactor χ s)⁻¹) ρ = 1 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hn⟩ := hΓ
    have heq :
      (fun s : ℂ => (DirichletCharacter.gammaFactor χ s)⁻¹) = (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) :=
      funext fun s => congrArg Inv.inv (he.gammaFactor_def s)
    rw [heq, hn, ← neg_mul]
    exact Gamma.analyticOrderAt_inverseGammaReal_neg_two_nat n
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hn⟩ := hΓ
    have heq :
      (fun s : ℂ => (DirichletCharacter.gammaFactor χ s)⁻¹) =
        (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) ∘ (fun s : ℂ => s + 1) :=
      funext fun s => congrArg Inv.inv (ho.gammaFactor_def s)
    have ha : AnalyticAt ℂ (fun s : ℂ => s + 1) ρ := analyticAt_id.add analyticAt_const
    have hd : deriv (fun s : ℂ => s + 1) ρ ≠ 0 := by
      have he := ((hasDerivAt_id ρ).add_const 1).deriv
      simp only [id_eq] at he
      exact he.trans_ne one_ne_zero
    rw [heq, analyticOrderAt_comp_of_deriv_ne_zero ha hd, hn, ← neg_mul]
    exact Gamma.analyticOrderAt_inverseGammaReal_neg_two_nat n

/-- For a nonprincipal primitive character, each gamma-forced zero in the closed
left half-plane is simple. Functional-equation nonvanishing of the completed
function and analytic-order multiplication give the exact residue multiplicity. -/
theorem dirichletLFunctionZeroMultiplicity_of_gamma_zero_eq_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) {ρ : ℂ} (hρ : ρ.re ≤ 0)
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) : dirichletLFunctionZeroMultiplicity χ ρ = 1 := by
  have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have hreflect : 1 ≤ ((1 : ℂ) - ρ).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith only [hρ]
  have hF := (DirichletCharacter.differentiable_completedLFunction hne).analyticAt ρ
  have hFne := completedLFunction_ne_zero_farLeft hp hne hinv hreflect
  have hG := (differentiable_inverse_gammaFactor χ).analyticAt ρ
  have heq :
    DirichletCharacter.LFunction χ =
      DirichletCharacter.completedLFunction χ *
        (fun s : ℂ => (DirichletCharacter.gammaFactor χ s)⁻¹) := by
    funext s
    exact
      (dirichletLFunction_eq_completed_div_gammaFactor χ s
            (Or.inr (dirichletCharacter_level_ne_one_of_ne_one hne))).trans
        (div_eq_mul_inv _ _)
  have ho : analyticOrderAt (DirichletCharacter.LFunction χ) ρ = 1 := by
    rw [heq, analyticOrderAt_mul hF hG, hF.analyticOrderAt_eq_zero.mpr hFne,
      analyticOrderAt_inverse_gammaFactor_of_zero hΓ, zero_add]
  unfold dirichletLFunctionZeroMultiplicity analyticOrderNatAt
  rw [ho, ENat.toNat_one]

/-- At a gamma-forced zero in the left half-plane, the logarithmic contribution
is exactly `-x^ρ/ρ²`. The primitive character has multiplicity one; this identity
removes the unknown multiplicity from the trivial-zero part of a finite ledger. -/
theorem dirichletLFunctionLogZeroContribution_of_gamma_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) {ρ : ℂ} (hρ : ρ.re ≤ 0)
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) (x : ℝ) :
    dirichletLFunctionLogZeroContribution x χ ρ = -(x : ℂ) ^ ρ / ρ ^ 2 := by
  simp only [dirichletLFunctionLogZeroContribution,
    dirichletLFunctionZeroMultiplicity_of_gamma_zero_eq_one hp hne hρ hΓ, Nat.cast_one, neg_mul,
    one_mul]

/-- At the same simple trivial zeros, the reciprocal contribution is exactly
`-x^(ρ-1)/(ρ*(ρ-1))`. This is the summand of the parity-dependent correction
series in the reciprocal explicit formula. -/
theorem dirichletLFunctionReciprocalZeroContribution_of_gamma_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hp : χ.IsPrimitive) (hne : χ ≠ 1) {ρ : ℂ} (hρ : ρ.re ≤ 0)
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) (x : ℝ) :
    dirichletLFunctionReciprocalZeroContribution x χ ρ = -(x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
  simp only [dirichletLFunctionReciprocalZeroContribution,
    dirichletLFunctionZeroMultiplicity_of_gamma_zero_eq_one hp hne hρ hΓ, Nat.cast_one, neg_mul,
    one_mul]

/-- Every zero of a complex Dirichlet gamma factor has nonpositive real part.
The even and odd formulas locate it at a nonpositive even integer or a
negative odd integer, respectively. This excludes the Mellin point one. -/
theorem gammaFactor_zero_re_nonpos {N : ℕ} {χ : DirichletCharacter ℂ N} {ρ : ℂ}
    (hΓ : DirichletCharacter.gammaFactor χ ρ = 0) : ρ.re ≤ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, rfl⟩ := hΓ
    simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.natCast_re, zero_mul, sub_zero]
    exact neg_nonpos.mpr (mul_nonneg zero_le_two (Nat.cast_nonneg n))
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hn⟩ := hΓ
    have hre := congrArg Complex.re hn
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re, Complex.mul_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.natCast_re, zero_mul, sub_zero] at hre
    linarith only [hre, Nat.cast_nonneg (α := ℝ) n]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
