/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformMass
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FinitePair

/-! # Variable-prefix three-character principal deficit -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The oscillating zero sums of three even characters satisfy the certified zero-mass upper
bound at cutoffs at least one. -/
theorem quarter_uniform_phase {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 0 < x) :
    -(∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm a x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm b x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm c x ρ).re <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) + (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  have hm :=
    quarter_uniform_mass hGRH.riemann a b c hP hQ hR (hGRH p a hpA) (hGRH q b hpB) (hGRH r c hpC)
      hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC (by linarith only [hX]) ht hA hB hC
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

/-- The three character sums are bounded by their contour remainders and the certified zero-mass
correction. -/
theorem quarter_uniform_summand {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand a x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand b x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand c x n).re <
      (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
          (refinedContourRemainder c x).re +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  have hz :=
    quarter_uniform_phase hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX ht
      hA hB hC (zero_lt_one.trans_le hx)
  have ha := congrArg Complex.re (refined_contour_formula hP hGRH hpA hnA hiA hx)
  have hb := congrArg Complex.re (refined_contour_formula hQ hGRH hpB hnB hiB hx)
  have hc := congrArg Complex.re (refined_contour_formula hR hGRH hpC hnC hiC hx)
  simp only [Complex.sub_re] at ha hb hc
  linarith only [hz, ha, hb, hc]

/-- Prime-prefix acceptance bounds the finite principal deficit using the three character
remainders. -/
theorem quarter_uniform_principal {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ)
    (hS : ∀ n ∈ s, (n : ℝ) ≤ X) :
    4 * (∑ n ∈ s, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re <
      (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
          (refinedContourRemainder c x).re +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  have hp : ∀ n ∈ s, ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3 := by
    intro n hn hΛ
    have ha :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) a
        (fun l hl hlX _ ↦ hA l hl hlX) (hS n hn) (Nat.coprime_one_right n) hΛ
    have hb :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) b
        (fun l hl hlX _ ↦ hB l hl hlX) (hS n hn) (Nat.coprime_one_right n) hΛ
    have hc :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) c
        (fun l hl hlX _ ↦ hC l hl hlX) (hS n hn) (Nat.coprime_one_right n) hΛ
    rw [ha, hb, hc, Complex.one_re]
    norm_num only
  have hpref := refined_three_principal_prefix a b c (zero_lt_one.trans_le hx) s ht hp
  have hup :=
    quarter_uniform_summand hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC hx
  linarith only [hpref, hup]

/-- At a cutoff at least one, the full prime prefix gives the finite principal deficit
inequality. -/
theorem quarter_uniform_cutoff {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
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
      (refinedContourRemainder a X).re + (refinedContourRemainder b X).re +
          (refinedContourRemainder c X).re +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  apply
    quarter_uniform_principal hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC (by linarith only [hX])
  intro n hn
  have hn' := (Finset.mem_Ioc.mp hn).2
  exact (Nat.cast_le.mpr hn').trans (Nat.floor_le (by linarith only [hX]))

end PseudoPrime.PrimeTestBounds.MillerRabin
