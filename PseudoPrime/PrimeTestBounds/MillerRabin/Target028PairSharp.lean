/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EulerMoment
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028PairNecessary

/-! # The sharp Gamma budget in the uniform triple comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under the three prime-prefix conditions, the refined cutoff deficit has
explicit conductor, reflected Euler, zero-mass and Gamma costs. The Gamma
cost is bounded by the sharper second-moment estimate. -/
theorem target028_cutoff_gamma_bounded {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
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
              (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_gamma_upper hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  have hx1 : (1 : ℝ) ≤ X := by linarith only [hX]
  rw [refined_conductor_sum p q r X, refined_conductor_profile hx1,
    refined_reflected_arch_eq_central a⁻¹ hiA hx1, refined_right_gamma_eq_central a hx,
    refined_central_gamma_pair_eq a heA hx] at h
  have hb := target028_reflected_euler_bound hx1
  have hg := target028_central_gamma_pair_le a heA hx
  linarith only [h, hg, hb]

/-- For a uniform Korselt product of three odd primes, if all primes up to
`X ≥ 1000` pass, then the principal deficit is bounded by explicit conductor,
Euler, Gamma and zero-mass costs. The principal sum remains to be estimated. -/
theorem target028_pair_gap_numeric {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X : ℝ} (hX : 1000 ≤ X)
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
              (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) +
          (3 / 8 : ℝ) * Real.log n -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  have hX' : (142 : ℝ) ≤ X := (by norm_num only : (142 : ℝ) ≤ 1000).trans hX
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
    target028_cutoff_gamma_bounded hGRH a b c (by linarith only [hpq]) (by linarith only [hpr])
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

/-- Under GRH, for a uniform three-prime Korselt product and `R ≥ 522`, passage
of every prime base up to `R²` forces the displayed strict scalar inequality. Combine
the one-sided principal gap with the explicit pair-character upper bound. -/
theorem target028_sharp_pair_necessary {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {R : ℝ} (hR : 522 ≤ R)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    R *
          (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
            (refinedSixPoleKernel.function (1 / 2)).re) -
        5 *
          ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
            ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
                ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
              R) -
        4 * |refinedWeightDeriv 1| *
            ((231 / 5000 : ℝ) * R + (1839 / 1000 : ℝ) * (2 * Real.log R) + 2) /
          R -
        4 * refinedWeight 1 *
          (((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt R +
            (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt R +
            (1839 / 1000 : ℝ) / R) <
      (2 * Real.log n) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              (R ^ 2) ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) +
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            (R ^ 2) ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) +
          (3 / 8 : ℝ) * Real.log n -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hX : (1000 : ℝ) ≤ R ^ 2 := by nlinarith only [hR]
  have hlower := target028_paper_gap_lower hGRH.riemann hR
  have hupper :=
    target028_pair_gap_numeric hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
      hvq hvr hX hpass
  exact lt_of_le_of_lt hlower hupper

/-- For a uniform three-prime Korselt product under GRH, the displayed scalar
certificate yields an actual prime Miller--Rabin witness at most `R²`. Use the
contrapositive of the paper-width necessary condition. -/
theorem target028_sharp_pair_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {R : ℝ} (hR : 522 ≤ R)
    (hcert :
      (2 * Real.log n) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                (R ^ 2) ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
              (R ^ 2) ^ (-(27 / 25 : ℝ)) *
              (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
                (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) +
            (3 / 8 : ℝ) * Real.log n -
          (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
        R *
            (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
              (refinedSixPoleKernel.function (1 / 2)).re) -
          5 *
            ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
              ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
                  ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
                R) -
          4 * |refinedWeightDeriv 1| *
              ((231 / 5000 : ℝ) * R + (1839 / 1000 : ℝ) * (2 * Real.log R) + 2) /
            R -
          4 * refinedWeight 1 *
            (((32 / 63 : ℝ) * (3 / 7) + (231 / 2500 : ℝ) * (7 / 3)) * Real.sqrt R +
              (231 / 2500 : ℝ) * (7 / 3) / Real.sqrt R +
              (1839 / 1000 : ℝ) / R)) :
    ∃ l : ℕ, l.Prime ∧ (l : ℝ) ≤ R ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  classical
  by_contra h
  have hall :
    ∀ l : ℕ, l.Prime → (l : ℝ) ≤ R ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
    intro l hl hlR
    exact Classical.byContradiction (fun hf ↦ h ⟨l, hl, hlR, hf⟩)
  exact
    (not_lt_of_ge hcert)
      (target028_sharp_pair_necessary hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
        hqK hrK hvq hvr hR hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
