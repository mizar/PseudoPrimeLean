/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThreeMass50000
public import PseudoPrime.LLS.PaperStatements.GaussianCharacterZeroBounds

/-! Joint oscillatory Gaussian zero bound with a certified Euler prefix. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

open PseudoPrime.LLS.PaperStatements in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, identify each Gaussian kernel zero norm with its completed-zero mass term. -/
theorem gaussian_kernel_zero_norm {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
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
  · have hz := completed_zero_of_divisor_ne_zero hne hD
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

/-- Under GRH, bound the oscillating Gaussian zero sum by its actual norm mass. -/
theorem gaussian_oscillating_zero_le_mass {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, LLS.PaperStatements.gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      gaussianActualZeroMass χ := by
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm
      LLS.PaperStatements.gaussianGammaMellinKernel hq hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm
          LLS.PaperStatements.gaussianGammaMellinKernel χ hx ρ).trans
      (gaussian_kernel_zero_norm hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact hn

/-- Under GRH and prime-prefix hypotheses, bound the three Gaussian oscillatory zero sums. -/
theorem gaussian_three_phase_50000 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 50000 ≤ X) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 0 < x) :
    -(∑' ρ : ℂ, LLS.PaperStatements.gaussianGammaMellinKernel.oscillatingZeroTerm a x ρ).re -
        (∑' ρ : ℂ, LLS.PaperStatements.gaussianGammaMellinKernel.oscillatingZeroTerm b x ρ).re -
        (∑' ρ : ℂ, LLS.PaperStatements.gaussianGammaMellinKernel.oscillatingZeroTerm c x ρ).re <
      (20115621 / 50000000 : ℝ) * (Real.log p + Real.log q + Real.log r) + 683 / 50 - 108 / 25 -
        4 * (1129059 / 200000 : ℝ) := by
  have hm :=
    gaussian_three_mass_50000 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC
  have hza := gaussian_oscillating_zero_le_mass hP hGRH hpA hnA hiA hx
  have hzb := gaussian_oscillating_zero_le_mass hQ hGRH hpB hnB hiB hx
  have hzc := gaussian_oscillating_zero_le_mass hR hGRH hpC hnC hiC hx
  have hra :=
    (abs_le.mp
        (Complex.abs_re_le_norm
          (∑' ρ : ℂ, LLS.PaperStatements.gaussianGammaMellinKernel.oscillatingZeroTerm a x ρ))).1
  have hrb :=
    (abs_le.mp
        (Complex.abs_re_le_norm
          (∑' ρ : ℂ, LLS.PaperStatements.gaussianGammaMellinKernel.oscillatingZeroTerm b x ρ))).1
  have hrc :=
    (abs_le.mp
        (Complex.abs_re_le_norm
          (∑' ρ : ℂ, LLS.PaperStatements.gaussianGammaMellinKernel.oscillatingZeroTerm c x ρ))).1
  linarith only [hm, hza, hzb, hzc, hra, hrb, hrc]

end PseudoPrime.PrimeTestBounds.MillerRabin
