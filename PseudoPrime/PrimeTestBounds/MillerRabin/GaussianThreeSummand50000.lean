/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThreePhase50000
public import PseudoPrime.LLS.PaperStatements.GaussianPrimitiveRemainderBounds

/-! Joint Gaussian arithmetic upper bound with separate conductor errors. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, combine three signed Gaussian remainders with the joint zero-mass gain. -/
theorem gaussian_three_summand_50000 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 20000 ≤ p) (hQ : 20000 ≤ q)
    (hR : 20000 ≤ r) (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1)
    (hnB : b ≠ 1) (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even)
    (heB : b.Even) (heC : c.Even) {X : ℝ} (hX : 50000 ≤ X)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, LLS.PaperStatements.gaussianGammaMellinKernel.summand a x n).re +
        (∑' n : ℕ, LLS.PaperStatements.gaussianGammaMellinKernel.summand b x n).re +
        (∑' n : ℕ, LLS.PaperStatements.gaussianGammaMellinKernel.summand c x n).re <
      (20115621 / 50000000 : ℝ) * (Real.log p + Real.log q + Real.log r) + 683 / 50 - 108 / 25 -
          4 * (1129059 / 200000 : ℝ) +
        (1536 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) *
          (((7 / 6 : ℝ) * (Real.log p + Real.log q + Real.log r) + 12) / Real.sqrt x) +
        (1419 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  have hza :=
    gaussian_three_phase_50000 hGRH a b c ((by norm_num only : 2 ≤ 20000).trans hP)
      ((by norm_num only : 2 ≤ 20000).trans hQ) ((by norm_num only : 2 ≤ 20000).trans hR) hpA hpB
      hpC hnA hnB hnC hiA hiB hiC heA heB heC hX ht hA hB hC (zero_lt_one.trans_le hx)
  have ha :=
    LLS.PaperStatements.re_gaussianRemainder_variable_GRH hP
      ((by norm_num only : 3 ≤ 20000).trans hP) le_rfl hpA hnA hiA hGRH hx
  have hb :=
    LLS.PaperStatements.re_gaussianRemainder_variable_GRH hQ
      ((by norm_num only : 3 ≤ 20000).trans hQ) le_rfl hpB hnB hiB hGRH hx
  have hc :=
    LLS.PaperStatements.re_gaussianRemainder_variable_GRH hR
      ((by norm_num only : 3 ≤ 20000).trans hR) le_rfl hpC hnC hiC hGRH hx
  simp only [Complex.add_re] at ha hb hc
  norm_num only [div_eq_mul_inv] at ha hb hc hza ⊢
  nlinarith only [hza, ha, hb, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
