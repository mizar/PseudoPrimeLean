/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformGammaPrefix
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformPrefixSharp
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaTailSeries

/-! # Uniform triple witness with negative Gamma saving -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, prime-level triviality and shifted scale at least twelve, the cutoff
deficit retains the negative Gamma and reflected Euler savings. -/
theorem quarter_uniform_gamma_negative {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X H : ℝ} (hX : 1 ≤ X) (hy : 12 ≤ Real.log X + 21 / 8)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    X ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log X) ^ 5) -
                3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
              H -
            4 * ∑ k ∈ s, refinedDualWeight X k +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  have h :=
    quarter_uniform_dual_prefix hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX s hS ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X, refined_conductor_sum p q r X,
    refined_conductor_profile hX, refined_reflected_arch_eq_central a⁻¹ hiA hX,
    refined_right_gamma_eq_central a hx, refined_central_gamma_pair_eq a heA hx] at h
  have hg := quarter_gamma_first_negative a heA hx hy
  linarith only [h, hg, hH]

/-- For a uniform Korselt triple, the accepted prime cutoff forces a
principal deficit with both Gamma and reflected Euler savings retained. -/
theorem quarter_uniform_pair_gap_negative {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 1 ≤ X)
    (hy : 12 ≤ Real.log X + 21 / 8) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re <
      (2 * Real.log n) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    X ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log X) ^ 5) -
                3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
              H -
            4 * ∑ k ∈ s, refinedDualWeight X k +
          (3 / 8 : ℝ) * Real.log n +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 *
          ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hpq : 2 ≤ p * q :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hpr : 2 ≤ p * r :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : r.Prime).pos)
  have hqr : 2 ≤ q * r :=
    (Fact.out : q.Prime).two_le.trans (Nat.le_mul_of_pos_right q (Fact.out : r.Prime).pos)
  have ha : a ≠ 1 := pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 2).trans_le hpq)
  have hb : b ≠ 1 := pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 2).trans_le hpr)
  have hc : c ≠ 1 := pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 2).trans_le hqr)
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
    quarter_uniform_gamma_negative hGRH a b c (by linarith only [hpq]) (by linarith only [hpr])
      (by linarith only [hqr]) (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc)
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hX hy hH s hS ht hA
      hB hC
  rw [pair_level_log_sum hnprod] at h
  convert h using 1
  ring

/-- A finite principal gap with the Gamma and reflected prefix savings
yields a rejecting prime for a uniform Korselt triple. -/
theorem quarter_uniform_witness_negative {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 1 ≤ X)
    (hy : 12 ≤ Real.log X + 21 / 8) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hgap :
      (2 * Real.log n) *
                    (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                      X ^ (-(27 / 25 : ℝ)) *
                      ((21 / 8 : ℝ) + Real.log X) ^ 5) -
                  3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
                H -
              4 * ∑ k ∈ s, refinedDualWeight X k +
            (3 / 8 : ℝ) * Real.log n +
            (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
          4 * ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
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
      (quarter_uniform_pair_gap_negative hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn
        hpK hqK hrK hvq hvr hX hy hH s hS hall)

/-- Under GRH and prime-level triviality, the negative Gamma estimate and sharp
closed Euler tail bound the uniform cutoff deficit. -/
theorem quarter_uniform_gamma_closed_negative {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X H : ℝ} (hX : 625 ≤ X) (hy : 12 ≤ Real.log X + 21 / 8)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
                (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                  X ^ (-(27 / 25 : ℝ)) *
                  ((21 / 8 : ℝ) + Real.log X) ^ 5) -
              3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
            H -
          4 * ∑ k ∈ s, refinedDualWeight X k +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have h :=
    quarter_uniform_dual_prefix_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA
      heB heC hX s hS ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X, refined_conductor_sum p q r X,
    refined_conductor_profile (by linarith only [hX]),
    refined_reflected_arch_eq_central a⁻¹ hiA (by linarith only [hX]),
    refined_right_gamma_eq_central a hx, refined_central_gamma_pair_eq a heA hx] at h
  have hg := quarter_gamma_first_negative a heA hx hy
  linarith only [h, hg, hH]

/-- The sharp closed Euler tail and the reflected prefix bound the uniform witness gap. -/
theorem quarter_uniform_gap_closed_negative {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 625 ≤ X)
    (hy : 12 ≤ Real.log X + 21 / 8) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re <
      (2 * Real.log n) *
                (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                  X ^ (-(27 / 25 : ℝ)) *
                  ((21 / 8 : ℝ) + Real.log X) ^ 5) -
              3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
            H -
          4 * ∑ k ∈ s, refinedDualWeight X k +
        (3 / 8 : ℝ) * Real.log n +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hpq : 2 ≤ p * q :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hpr : 2 ≤ p * r :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : r.Prime).pos)
  have hqr : 2 ≤ q * r :=
    (Fact.out : q.Prime).two_le.trans (Nat.le_mul_of_pos_right q (Fact.out : r.Prime).pos)
  have ha : a ≠ 1 := pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 2).trans_le hpq)
  have hb : b ≠ 1 := pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 2).trans_le hpr)
  have hc : c ≠ 1 := pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 2).trans_le hqr)
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
    quarter_uniform_gamma_closed_negative hGRH a b c (by linarith only [hpq])
      (by linarith only [hpr]) (by linarith only [hqr])
      (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc)
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hX hy hH s hS ht hA
      hB hC
  rw [pair_level_log_sum hnprod] at h
  convert h using 1
  ring

/-- The sharp closed Euler tail and the reflected prefix bound the uniform witness gap. -/
theorem quarter_uniform_witness_closed_negative {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 625 ≤ X)
    (hy : 12 ≤ Real.log X + 21 / 8) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hgap :
      (2 * Real.log n) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    X ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log X) ^ 5) -
                3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
              H -
            4 * ∑ k ∈ s, refinedDualWeight X k +
          (3 / 8 : ℝ) * Real.log n +
          -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
          4 * quarterEulerClosedTailCap X ≤
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
      (quarter_uniform_gap_closed_negative hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn
        hpK hqK hrK hvq hvr hX hy hH s hS hall)

/-- Under GRH and prime-level triviality, the closed Euler-tail bound retains
the explicit negative Gamma baseline in the uniform cutoff deficit. -/
theorem quarter_uniform_gamma_closed_baseline {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X H : ℝ} (hX : 625 ≤ X) (hy : 12 ≤ Real.log X + 21 / 8)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (s : Finset ℕ)
    (hS : ∀ k ∈ s, (k : ℝ) ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
                (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                  X ^ (-(27 / 25 : ℝ)) *
                  ((21 / 8 : ℝ) + Real.log X) ^ 5) -
              3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
              4 * quarterGammaDensity (Real.log X + 21 / 8) +
            H -
          4 * ∑ k ∈ s, refinedDualWeight X k +
        (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  have h :=
    quarter_uniform_dual_prefix_closed hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA
      heB heC hX s hS ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  rw [refined_three_nonEuler_even a b c hiA hiB hiC heA heB heC X, refined_conductor_sum p q r X,
    refined_conductor_profile (by linarith only [hX]),
    refined_reflected_arch_eq_central a⁻¹ hiA (by linarith only [hX]),
    refined_right_gamma_eq_central a hx, refined_central_gamma_pair_eq a heA hx] at h
  have hg := quarter_gamma_first_baseline a heA hx hy
  linarith only [h, hg, hH]

/-- The sharp closed Euler tail and the reflected prefix bound the uniform witness gap. -/
theorem quarter_uniform_gap_closed_baseline {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 625 ≤ X)
    (hy : 12 ≤ Real.log X + 21 / 8) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re <
      (2 * Real.log n) *
                (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                  X ^ (-(27 / 25 : ℝ)) *
                  ((21 / 8 : ℝ) + Real.log X) ^ 5) -
              3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
              4 * quarterGammaDensity (Real.log X + 21 / 8) +
            H -
          4 * ∑ k ∈ s, refinedDualWeight X k +
        (3 / 8 : ℝ) * Real.log n +
        -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap X := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hpq : 2 ≤ p * q :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : q.Prime).pos)
  have hpr : 2 ≤ p * r :=
    (Fact.out : p.Prime).two_le.trans (Nat.le_mul_of_pos_right p (Fact.out : r.Prime).pos)
  have hqr : 2 ≤ q * r :=
    (Fact.out : q.Prime).two_le.trans (Nat.le_mul_of_pos_right q (Fact.out : r.Prime).pos)
  have ha : a ≠ 1 := pair_character_ne_one hsq hpqn (hp.mul hq) ((by decide : 1 < 2).trans_le hpq)
  have hb : b ≠ 1 := pair_character_ne_one hsq hprn (hp.mul hr) ((by decide : 1 < 2).trans_le hpr)
  have hc : c ≠ 1 := pair_character_ne_one hsq hqrn (hq.mul hr) ((by decide : 1 < 2).trans_le hqr)
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
    quarter_uniform_gamma_closed_baseline hGRH a b c (by linarith only [hpq])
      (by linarith only [hpr]) (by linarith only [hqr])
      (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc)
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hX hy hH s hS ht hA
      hB hC
  rw [pair_level_log_sum hnprod] at h
  convert h using 1
  ring

/-- The sharp closed Euler tail and the reflected prefix bound the uniform witness gap. -/
theorem quarter_uniform_witness_closed_baseline {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 625 ≤ X)
    (hy : 12 ≤ Real.log X + 21 / 8) (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (s : Finset ℕ) (hS : ∀ k ∈ s, (k : ℝ) ≤ X)
    (hgap :
      (2 * Real.log n) *
                  (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                    X ^ (-(27 / 25 : ℝ)) *
                    ((21 / 8 : ℝ) + Real.log X) ^ 5) -
                3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) -
                4 * quarterGammaDensity (Real.log X + 21 / 8) +
              H -
            4 * ∑ k ∈ s, refinedDualWeight X k +
          (3 / 8 : ℝ) * Real.log n +
          -(3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
          4 * quarterEulerClosedTailCap X ≤
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
      (quarter_uniform_gap_closed_baseline hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn
        hpK hqK hrK hvq hvr hX hy hH s hS hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
