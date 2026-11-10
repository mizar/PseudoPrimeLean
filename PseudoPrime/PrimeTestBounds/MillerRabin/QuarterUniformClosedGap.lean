/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformCutoff
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentTailClosed
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformPairGap

/-! Sharp zero-phase and contour estimates using the closed Euler tail. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and prime-level triviality, the real parts of the three oscillating zero sums
are bounded by the sharp zero mass and the closed Euler-tail envelope. -/
theorem quarter_uniform_phase_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 0 < x) :
    -(∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm a x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm b x ρ).re -
        (∑' ρ : ℂ, refinedSixPoleKernel.oscillatingZeroTerm c x ρ).re <
      (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have hm :=
    quarter_uniform_mass_tail_closed hGRH.riemann a b c hP hQ hR (hGRH p a hpA) (hGRH q b hpB)
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

/-- The three character sums inherit the sharp closed-tail zero-phase bound. -/
theorem quarter_uniform_summand_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, refinedSixPoleKernel.summand a x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand b x n).re +
        (∑' n : ℕ, refinedSixPoleKernel.summand c x n).re <
      (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
        (refinedContourRemainder c x).re +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have hz :=
    quarter_uniform_phase_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC (zero_lt_one.trans_le hx)
  have ha := congrArg Complex.re (refined_contour_formula hP hGRH hpA hnA hiA hx)
  have hb := congrArg Complex.re (refined_contour_formula hQ hGRH hpB hnB hiB hx)
  have hc := congrArg Complex.re (refined_contour_formula hR hGRH hpC hnC hiC hx)
  simp only [Complex.sub_re] at ha hb hc
  linarith only [hz, ha, hb, hc]

/-- The finite principal deficit is bounded using the sharp closed-tail character estimates. -/
theorem quarter_uniform_principal_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) {x : ℝ} (hx : 1 ≤ x) (s : Finset ℕ)
    (hS : ∀ n ∈ s, (n : ℝ) ≤ X) :
    4 * (∑ n ∈ s, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re <
      (refinedContourRemainder a x).re + (refinedContourRemainder b x).re +
        (refinedContourRemainder c x).re +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
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
    quarter_uniform_summand_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB
      heC hX ht hA hB hC hx
  linarith only [hpref, hup]

/-- The full prime prefix satisfies the sharp closed-tail principal deficit inequality. -/
theorem quarter_uniform_cutoff_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (refinedContourRemainder a X).re + (refinedContourRemainder b X).re +
        (refinedContourRemainder c X).re +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  apply
    quarter_uniform_principal_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB
      heC hX ht hA hB hC (by linarith only [hX])
  intro n hn
  have hn' := (Finset.mem_Ioc.mp hn).2
  exact (Nat.cast_le.mpr hn').trans (Nat.floor_le (by linarith only [hX]))

/-- Under GRH, the closed Euler-tail bound controls this contour or Gamma expression. -/
theorem quarter_uniform_dual_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      refinedContourNonEuler a X + refinedContourNonEuler b X + refinedContourNonEuler c X +
        refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have htInv : ∀ k : ℕ, -1 ≤ (a⁻¹ k).re + (b⁻¹ k).re + (c⁻¹ k).re := by
    intro k
    simpa only [refined_inv_char_re] using ht k
  have hc :=
    quarter_uniform_cutoff_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB
      heC hX ht hA hB hC
  have hd :=
    refined_three_contour_upper a b c hpA hpB hpC hnA hnB hnC hiA hiB hiC (by linarith only [hX])
      htInv
  linarith only [hc, hd]

/-- Under GRH, the closed Euler-tail bound controls this contour or Gamma expression. -/
theorem quarter_uniform_gamma_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 625 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
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
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have h :=
    quarter_uniform_dual_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X] at h
  exact h

/-- Under GRH, the closed Euler-tail bound controls this contour or Gamma expression. -/
theorem quarter_uniform_gamma_first_closed {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X H : ℝ} (hX : 625 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
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
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
          3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
        H +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have h :=
    quarter_uniform_gamma_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  have hy : 0 ≤ Real.log X + 21 / 8 := by
    have hh := Real.log_nonneg (by linarith only [hX])
    linarith only [hh]
  rw [refined_conductor_sum p q r X, refined_conductor_profile (by linarith only [hX]),
    refined_reflected_arch_eq_central a⁻¹ hiA (by linarith only [hX]),
    refined_right_gamma_eq_central a hx, refined_central_gamma_pair_eq a heA hx] at h
  have hg := quarter_gamma_central_first_pole a heA hx hy
  change
    (refinedCentralGammaPair a X).re + quarterGammaFirstCorrection (Real.log X + 21 / 8) ≤
      (13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 at hg
  linarith only [h, hg, hH]

end PseudoPrime.PrimeTestBounds.MillerRabin
