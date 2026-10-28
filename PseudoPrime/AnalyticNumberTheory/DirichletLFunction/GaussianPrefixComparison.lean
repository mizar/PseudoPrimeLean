/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.LLS.GammaCheckpoint35000
public import PseudoPrime.LLS.GaussianPrefixComparison2

/-! # Signed Gaussian prefix comparison with arbitrary certified cutoff mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

variable {N : ℕ} {P : ℝ}

/-- Given a certified Gaussian prefix mass and triviality on its prime bases,
transfer the signed prefix gain through this comparison, retaining the exact conductor coefficient.
The result is used by the next stage of the constant-principal MR comparison. -/
theorem gaussian_zeroMass_prefix_lt
    (hprefix : P ≤ ∑ n ∈ Finset.Ioc 0 N, Analysis.gaussianResolventMangoldtWeight n) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hRiemann : RiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ N → χ p = 1) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) +
        Analysis.gaussianPairedEulerTail χ (Finset.Ioc 0 (N : ℕ)) <
      (20115621 / 50000000 : ℝ) * Real.log q + (12871 / 1000 - 2 * P) := by
  let B := Finset.Ioc 0 (N : ℕ)
  have h := gaussian_zeroMass_add_pairedTail_lt_principal_prefix hq hRH hRiemann hp hne hinv B
  have htrivB : ∑ m ∈ B, (1 - (χ m).re) * Analysis.gaussianResolventMangoldtWeight m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hΛ : ArithmeticFunction.vonMangoldt m = 0
    · simp only [Analysis.gaussianResolventMangoldtWeight, hΛ, zero_mul, mul_zero]
    · obtain ⟨p, r, hp, hr, rfl⟩ :=
        (isPrimePow_nat_iff (n := m)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
      have hpbound : (p : ℝ) ≤ N := by
        calc
          (p : ℝ) ≤ (p ^ r : ℕ) := by exact_mod_cast Nat.le_pow hr
          _ ≤ N := by exact_mod_cast (Finset.mem_Ioc.mp hm).2
      simp only [Analysis.gaussianResolventMangoldtWeight, Nat.cast_pow, map_pow,
        hsmall p hp hpbound, one_pow, Complex.one_re, sub_self, zero_mul]
  dsimp only [B] at h
  rw [htrivB, add_zero] at h
  linarith only [h, hprefix]

/-- Under primitive nonprincipal GRH, the kernel zero-term norm is its nonnegative
completed multiplicity times the Gaussian norm on the critical line. The divisor-zero split
handles all complex inputs and connects zero-mass bounds to oscillating kernel sums. -/
private theorem gaussian_kernel_zero_norm {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ρ : ℂ) :
    ‖LLS.PaperStatements.gaussianGammaMellinKernel.kernelZeroTerm χ ρ‖ =
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

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
