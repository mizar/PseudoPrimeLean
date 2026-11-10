/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosedGap

/-! Uniform Korselt witness using the sharp closed Euler-tail bound. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sharp closed-tail inequality controls the uniform Korselt prime-witness gap. -/
theorem quarter_uniform_pair_gap_closed {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 625 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re <
      (2 * Real.log n) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                X ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log X) ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
          3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
        H +
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
    quarter_uniform_gamma_first_closed hGRH a b c (by linarith only [hpq]) (by linarith only [hpr])
      (by linarith only [hqr]) (pair_character_primitive hsq hpqn (hp.mul hq))
      (pair_character_primitive hsq hprn (hp.mul hr))
      (pair_character_primitive hsq hqrn (hq.mul hr)) ha hb hc (inv_ne_one.mpr ha)
      (inv_ne_one.mpr hb) (inv_ne_one.mpr hc)
      (pair_character_even_of_korselt hn ho hp hq hpK hqK hvq)
      (pair_character_even_of_korselt hn ho hp hr hpK hrK hvr)
      (pair_character_even_of_korselt hn ho hq hr hqK hrK (hvr.trans hvq.symm)) hX hH ht hA hB hC
  rw [pair_level_log_sum hnprod] at h
  convert h using 1
  ring

/-- The sharp closed-tail inequality controls the uniform Korselt prime-witness gap. -/
theorem quarter_uniform_pair_witness_closed {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q]
    [NeZero r] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)]
    [Fact (2 < r)] (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X H : ℝ} (hX : 625 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H)
    (hgap :
      (2 * Real.log n) *
                (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                  X ^ (-(27 / 25 : ℝ)) *
                  ((21 / 8 : ℝ) + Real.log X) ^ 5) +
              (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
            3 * quarterGammaFirstCorrection (Real.log X + 21 / 8) +
          H +
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
      (quarter_uniform_pair_gap_closed hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
        hqK hrK hvq hvr hX hH hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
