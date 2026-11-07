/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerMassCertified
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeros

/-! Three-character oscillatory zero bound for the refined kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a nonprincipal character, the zero-term norm is its nonnegative multiplicity
times the kernel norm. -/
theorem refined_kernel_zero_norm {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1)
    (ρ : ℂ) :
    ‖refinedSixPoleKernel.kernelZeroTerm χ ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖ := by
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hd : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
  unfold LLS.PaperStatements.MellinKernel.kernelZeroTerm
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hd]

/-- Under GRH, the oscillatory zero sum is bounded in norm by the actual refined zero mass. -/
theorem refined_oscillating_zero_le_mass {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm χ x ρ‖ ≤ sixMass χ := by
  have hs :=
    LLS.PaperStatements.MellinKernel.summable_oscillatingZeroTerm refinedSixPoleKernel hq hGRH hp
      hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (LLS.PaperStatements.MellinKernel.norm_oscillatingZeroTerm refinedSixPoleKernel χ hx ρ).trans
      (refined_kernel_zero_norm hne ρ)
  rw [tsum_congr he] at hn
  exact hn

/-- Under GRH and the prime-prefix assumptions, the three oscillatory zero sums
satisfy the certified mass bound. -/
theorem refined_three_phase_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 0 < x) :
    -(∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm a x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm b x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm c x ρ).re <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hm :=
    refined_three_mass_even_certified hGRH.riemann a b c hP hQ hR (hGRH p a hpA) (hGRH q b hpB)
      (hGRH r c hpC) hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX ht hA hB hC
  have hza := refined_oscillating_zero_le_mass hP hGRH hpA hnA hiA hx
  have hzb := refined_oscillating_zero_le_mass hQ hGRH hpB hnB hiB hx
  have hzc := refined_oscillating_zero_le_mass hR hGRH hpC hnC hiC hx
  have hra :=
    (abs_le.mp
        (Complex.abs_re_le_norm (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm a x ρ))).1
  have hrb :=
    (abs_le.mp
        (Complex.abs_re_le_norm (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm b x ρ))).1
  have hrc :=
    (abs_le.mp
        (Complex.abs_re_le_norm (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm c x ρ))).1
  linarith only [hm, hza, hzb, hzc, hra, hrb, hrc]

end PseudoPrime.PrimeTestBounds.MillerRabin
