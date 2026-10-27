/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianResolventZeroMass
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianPrincipalEulerBudget
public import PseudoPrime.LLS.GaussianPrincipalEulerBudgetExtensions
public import PseudoPrime.LLS.GaussianKernel
public import PseudoPrime.LLS.MellinKernelPrimitiveAverage
public import PseudoPrime.LLS.MellinKernelZeros

/-! # Explicit oscillating zero-sum bound for the Gaussian Gamma kernel

The kernel-certified finite-conductor Gaussian mass controls the actual oscillating
zero sum at every positive scale. No majorant or grid hypothesis remains in the final bound.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- Under primitive nonprincipal GRH with nonprincipal inverse, the Gaussian
kernel zero-term norm equals its nonnegative completed multiplicity times the actual
Gaussian norm at ρ-1/2. A nonzero multiplicity lies on the critical line; a zero
multiplicity makes both sides vanish. This identifies the zero-mass estimate with kernel terms. -/
private theorem norm_gaussian_kernelZeroTerm_eq {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ρ : ℂ) :
    ‖gaussianGammaMellinKernel.kernelZeroTerm χ ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖ := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · change
      ‖(D : ℂ) * Analysis.gaussianGammaFunction (Complex.I * ρ.im)‖ =
        (D : ℝ) * ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖
    rw [hD]
    norm_num only [Int.cast_zero, zero_mul, norm_zero]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
    have he : Complex.I * (ρ.im : ℂ) + 1 / 2 = ρ := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re,
          zero_add]
        exact hr.symm
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im,
          zero_div, add_zero]
    have hDn : (0 : ℝ) ≤ D := by
      have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
        (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    change ‖(D : ℂ) * Analysis.gaussianGammaFunction (Complex.I * ρ.im)‖ = _
    have he' : Complex.I * (ρ.im : ℂ) = ρ - 1 / 2 := by
      calc
        _ = (Complex.I * (ρ.im : ℂ) + 1 / 2) - 1 / 2 := by ring
        _ = _ := by rw [he]
    rw [he', norm_mul, Complex.norm_intCast, abs_of_nonneg hDn]

/-- Under primitive nonprincipal GRH with nonprincipal inverse and modulus at
least two, the grid conditions bound the actual oscillating Gaussian zero sum at every
positive scale by 161/400 times log m plus 1811. Use absolute convergence and the
norm identity to transfer the finite-conductor mass estimate. -/
theorem norm_gaussian_oscillatingZeroSum_lt_of_grid {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x)
    (hnodes :
      ∀ j : ℕ, j ≤ 16000 → 9 / 100000 ≤ Analysis.gaussianResolventScaledGap ((j : ℝ) / 1000)) :
    ‖∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (161 / 400 : ℝ) * Real.log m + 1811 := by
  have hs :=
    MellinKernel.summable_oscillatingZeroTerm gaussianGammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gaussianGammaMellinKernel χ hx ρ).trans
      (norm_gaussian_kernelZeroTerm_eq hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact
    hn.trans_lt
      (AnalyticNumberTheory.DirichletLFunction.gaussian_zeroMass_lt_target_of_grid hnodes hm
        (hGRH m χ hp) hp hne hinv)

/-- Under primitive nonprincipal GRH with nonprincipal inverse and modulus at
least two, the actual oscillating Gaussian zero sum is below 161/400 times log m
plus 1811 at every positive scale. Apply the kernel-certified grid to the common
consumer theorem. No additional numerical or analytic mass hypothesis remains. -/
theorem norm_gaussian_oscillatingZeroSum_lt {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (161 / 400 : ℝ) * Real.log m + 1811 := by
  exact
    norm_gaussian_oscillatingZeroSum_lt_of_grid hm hGRH hp hne hinv hx
      Analysis.gaussianResolvent_grid_lower

/-- Under primitive nonprincipal GRH, the actual oscillating Gaussian zero sum
has additive cost 12871/1000 at every positive scale. Retain the exact signed
Euler weight and use the principal xi budget rather than absolute node errors. -/
theorem norm_gaussian_oscillatingZeroSum_lt_principal {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (20115621 / 50000000 : ℝ) * Real.log m + 12871 / 1000 := by
  have hs :=
    MellinKernel.summable_oscillatingZeroTerm gaussianGammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gaussianGammaMellinKernel χ hx ρ).trans
      (norm_gaussian_kernelZeroTerm_eq hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact
    hn.trans_lt
      (AnalyticNumberTheory.DirichletLFunction.gaussian_zeroMass_lt_principal_uniform hm
        (hGRH m χ hp) hGRH.riemann hp hne hinv)

/-- If a primitive character is trivial on the 50000 prefix, its Gaussian
oscillating zero sum has additive constant 159169/50000. Transfer the Gamma
prefix gain through the signed Euler budget and discard the nonnegative paired tail. -/
theorem norm_gaussian_oscillatingZeroSum_lt_prefix_gain {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ p = 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (20115621 / 50000000 : ℝ) * Real.log m + 159169 / 50000 := by
  have hs :=
    MellinKernel.summable_oscillatingZeroTerm gaussianGammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gaussianGammaMellinKernel χ hx ρ).trans
      (norm_gaussian_kernelZeroTerm_eq hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  let B := Finset.Ioc 0 (50000 : ℕ)
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gaussian_zeroMass_add_pairedTail_lt_prefix_gain hm
      (hGRH m χ hp) hGRH.riemann hp hne hinv hsmall
  have ht := Analysis.gaussianPairedEulerTail_nonneg χ B
  dsimp only [B] at hz ht
  have hzero :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (20115621 / 50000000 : ℝ) * Real.log m + 159169 / 50000 := by
    linarith only [hz, ht]
  exact hn.trans_lt hzero

/-- If a primitive character is trivial on the 1000 prefix, its Gaussian
oscillating zero sum has additive constant 5969/1000. Apply the transferred
prefix bound and discard the nonnegative paired tail. -/
theorem norm_gaussian_oscillatingZeroSum_lt_prefix1000_gain {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1000 → χ p = 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (20115621 / 50000000 : ℝ) * Real.log m + 5969 / 1000 := by
  have hs :=
    MellinKernel.summable_oscillatingZeroTerm gaussianGammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gaussianGammaMellinKernel χ hx ρ).trans
      (norm_gaussian_kernelZeroTerm_eq hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  let B := Finset.Ioc 0 (1000 : ℕ)
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gaussian_zeroMass_add_pairedTail_lt_prefix1000_gain hm
      (hGRH m χ hp) hGRH.riemann hp hne hinv hsmall
  have ht := Analysis.gaussianPairedEulerTail_nonneg χ B
  dsimp only [B] at hz ht
  have hzero :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) <
      (20115621 / 50000000 : ℝ) * Real.log m + 5969 / 1000 := by
    linarith only [hz, ht]
  exact hn.trans_lt hzero

end PseudoPrime.LLS.PaperStatements
