/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerPrefix252
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FinitePair
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028LogSixIntegral

/-! # Finite-cutoff comparison from 252 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The oscillating zero sums of three even characters satisfy the certified zero-mass upper
bound at cutoffs at least 252. -/
theorem target028_phase_upper252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 0 < x) :
    -(∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm a x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm b x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm c x ρ).re <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hm :=
    target028_three_mass_prefix252 hGRH.riemann a b c hP hQ hR (hGRH p a hpA) (hGRH q b hpB)
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

/-- The three character sums are bounded by their contour remainders and the certified zero-mass
correction. -/
theorem target028_summand_upper252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand a x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand b x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand c x n).re <
      (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
          (refinedContourRemainder c x).re +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hz :=
    target028_phase_upper252 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC (zero_lt_one.trans_le hx)
  have ha := congrArg Complex.re (refined_contour_formula hP hGRH hpA hnA hiA hx)
  have hb := congrArg Complex.re (refined_contour_formula hQ hGRH hpB hnB hiB hx)
  have hc := congrArg Complex.re (refined_contour_formula hR hGRH hpC hnC hiC hx)
  simp only [Complex.sub_re] at ha hb hc
  linarith only [hz, ha, hb, hc]

/-- Prime-prefix acceptance bounds the finite principal deficit using the three character
remainders. -/
theorem target028_principal_upper252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ)
    (hS : ∀ n ∈ s, (n : ℝ) ≤ X) :
    4 * (∑ n ∈ s, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re <
      (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
          (refinedContourRemainder c x).re +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
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
    target028_summand_upper252 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC hx
  linarith only [hpref, hup]

/-- At a cutoff at least 252, the full prime prefix gives the finite principal deficit
inequality. -/
theorem target028_cutoff_upper252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (refinedContourRemainder a X).re + (refinedContourRemainder b X).re +
          (refinedContourRemainder c X).re +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  apply
    target028_principal_upper252 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC (by linarith only [hX])
  intro n hn
  have hn' := (Finset.mem_Ioc.mp hn).2
  exact (Nat.cast_le.mpr hn').trans (Nat.floor_le (by linarith only [hX]))

/-- The three-character deficit is bounded by the non-Euler contours and one principal reflected
Euler term. -/
theorem target028_dual_upper252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      refinedContourNonEuler a X + refinedContourNonEuler b X + refinedContourNonEuler c X +
          refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have htInv : ∀ k : ℕ, -1 ≤ (a⁻¹ k).re + (b⁻¹ k).re + (c⁻¹ k).re := by
    intro k
    simpa only [refined_inv_char_re] using ht k
  have hc :=
    target028_cutoff_upper252 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC
  have hd :=
    refined_three_contour_upper a b c hpA hpB hpC hnA hnB hnC hiA hiB hiC (by linarith only [hX])
      htInv
  linarith only [hc, hd]

/-- For even characters, the non-Euler contours split into conductor and common Gamma terms. -/
theorem target028_gamma_upper252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
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
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    target028_dual_upper252 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X] at h
  exact h

/-- The certified Gamma and reflected Euler bounds make the finite principal deficit explicit. -/
theorem target028_gamma_bounded252 {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 252 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              X ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log X) ^ 5) +
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              ((720 : ℝ) / (29 / 50 : ℝ) ^ 7 + 200)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    target028_gamma_upper252 hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC hX
      ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  have hx1 : (1 : ℝ) ≤ X := by linarith only [hX]
  rw [refined_conductor_sum p q r X, refined_conductor_profile hx1,
    refined_reflected_arch_eq_central a⁻¹ hiA hx1, refined_right_gamma_eq_central a hx,
    refined_central_gamma_pair_eq a heA hx] at h
  have hb := target028_reflected_euler_sharp hx1
  have hg := target028_central_gamma_pair_le a heA hx
  linarith only [h, hg, hb]

/-- For a uniform three-prime Korselt product, acceptance through the cutoff forces the explicit
principal gap. -/
theorem target028_pair_gap252 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X : ℝ} (hX : 252 ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re <
      (2 * Real.log n) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              X ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log X) ^ 5) +
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              ((720 : ℝ) / (29 / 50 : ℝ) ^ 7 + 200)) +
          (3 / 8 : ℝ) * Real.log n -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hX' : (142 : ℝ) ≤ X := (by norm_num only : (142 : ℝ) ≤ 252).trans hX
  have hpq :=
    pair_level_large_of_all_pass hn ho (Fact.out : p.Prime) (Fact.out : q.Prime) hpn hqn hX' hpass
  have hpr :=
    pair_level_large_of_all_pass hn ho (Fact.out : p.Prime) (Fact.out : r.Prime) hpn hrn hX' hpass
  have hqr :=
    pair_level_large_of_all_pass hn ho (Fact.out : q.Prime) (Fact.out : r.Prime) hqn hrn hX' hpass
  have ha : a ≠ 1 :=
    pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 20000).trans_le hpq)
  have hb : b ≠ 1 :=
    pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 20000).trans_le hpr)
  have hc : c ≠ 1 :=
    pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 20000).trans_le hqr)
  have ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re := by
    intro k
    simpa only [Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hq hpn hqn hpqn hpK hqK hvq l (hpass l hl hlX)
  have hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1 := by
    intro l hl hlX
    exact pair_character_nat_eq_one hn ho hp hr hpn hrn hprn hpK hrK hvr l (hpass l hl hlX)
  have hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1 := by
    intro l hl hlX
    exact
      pair_character_nat_eq_one hn ho hq hr hqn hrn hqrn hqK hrK (hvr.trans hvq.symm) l
        (hpass l hl hlX)
  have h :=
    target028_gamma_bounded252 hGRH a b c (by linarith only [hpq]) (by linarith only [hpr])
      (by linarith only [hqr]) (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc)
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hX ht hA hB hC
  rw [pair_level_log_sum hnprod] at h
  convert h using 1
  ring

/-- For a uniform three-prime Korselt product, the displayed finite principal gap yields a
rejecting prime. -/
theorem target028_finite_pair252 {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X : ℝ} (hX : 252 ≤ X)
    (hgap :
      (2 * Real.log n) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                X ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log X) ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
              X ^ (-(27 / 25 : ℝ)) *
              (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
                ((720 : ℝ) / (29 / 50 : ℝ) ^ 7 + 200)) +
            (3 / 8 : ℝ) * Real.log n -
          (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
        4 *
            (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
              (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
          (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl hlX
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl, hlX, hf⟩)
  exact
    (not_lt_of_ge hgap)
      (target028_pair_gap252 hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
        hvq hvr hX hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
