/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028LogSixIntegral

/-! # Variable-prefix three-character dual contour comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The three-character deficit is bounded by the non-Euler contours and one principal reflected
Euler term. -/
theorem quarter_uniform_dual {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      refinedContourNonEuler a X + refinedContourNonEuler b X + refinedContourNonEuler c X +
          refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  have htInv : ∀ k : ℕ, -1 ≤ (a⁻¹ k).re + (b⁻¹ k).re + (c⁻¹ k).re := by
    intro k
    simpa only [refined_inv_char_re] using ht k
  have hc :=
    quarter_uniform_cutoff hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX ht
      hA hB hC
  have hd :=
    refined_three_contour_upper a b c hpA hpB hpC hnA hnB hnC hiA hiB hiC (by linarith only [hX])
      htInv
  linarith only [hc, hd]

/-- For even characters, the non-Euler contours split into conductor and common Gamma terms. -/
theorem quarter_uniform_gamma {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Complex.log p * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) X⁻¹ : ℂ)).re +
          (Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) X⁻¹ : ℂ)).re +
          (Complex.log r * (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) X⁻¹ : ℂ)).re +
          3 * (refinedReflectedArchimedean a⁻¹ X + refinedRightGamma a X).re +
          refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  have h :=
    quarter_uniform_dual hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX ht
      hA hB hC
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
