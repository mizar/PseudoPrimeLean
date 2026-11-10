/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformDual
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedReflectedPrefix

/-! # Reflected prefix improvement of the uniform-triple cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The uniform triple cutoff inequality includes the finite reflected Euler
saving. Prime-level triviality determines the character values on its support. -/
theorem quarter_uniform_dual_prefix {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1 ≤ X) (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      refinedContourNonEuler a X + refinedContourNonEuler b X + refinedContourNonEuler c X +
              refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X -
            4 * ∑ k ∈ s, refinedDualWeight X k +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  have hp : ∀ k ∈ s, ArithmeticFunction.vonMangoldt k ≠ 0 → (a k).re + (b k).re + (c k).re = 3 := by
    intro k hk hΛ
    have h1 :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) a
        (fun l hl hlX _ ↦ hA l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
    have h2 :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) b
        (fun l hl hlX _ ↦ hB l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
    have h3 :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) c
        (fun l hl hlX _ ↦ hC l hl hlX) (hS k hk) (Nat.coprime_one_right k) hΛ
    rw [h1, h2, h3, Complex.one_re]
    norm_num only
  have hc :=
    quarter_uniform_cutoff hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX ht
      hA hB hC
  have hd :=
    refined_contour_prefix a b c hpA hpB hpC hnA hnB hnC hiA hiB hiC (by linarith only [hX]) s ht hp
  linarith only [hc, hd]

end PseudoPrime.PrimeTestBounds.MillerRabin
