/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleOneSided
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePairNumeric

/-! # Explicit paper-width necessary condition for the three-prime branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, for a uniform three-prime Korselt product and `R ≥ 522`, passage
of every prime base up to `R²` forces the displayed strict scalar inequality. Combine
the one-sided principal gap with the explicit pair-character upper bound. -/
theorem refined_pair_paper_necessary {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
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
          ((231 / 5000 : ℝ) * (6889 / 2700) +
            ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
                ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
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
          5 * (27 / 25 : ℝ) ^ 5 +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            (R ^ 2) ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
          (3 / 8 : ℝ) * Real.log n -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have hX : (1000 : ℝ) ≤ R ^ 2 := by nlinarith only [hR]
  have hlower := refined_paper_gap_lower hGRH.riemann hR
  have hupper :=
    refined_pair_gap_numeric hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK
      hvq hvr hX hpass
  exact lt_of_le_of_lt hlower hupper

/-- For a uniform three-prime Korselt product under GRH, the displayed scalar
certificate yields an actual prime Miller--Rabin witness at most `R²`. Use the
contrapositive of the paper-width necessary condition. -/
theorem refined_pair_paper_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
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
            5 * (27 / 25 : ℝ) ^ 5 +
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
              (R ^ 2) ^ (-(27 / 25 : ℝ)) *
              (((21 / 8 : ℝ) + Real.log (R ^ 2)) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
                (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
            (3 / 8 : ℝ) * Real.log n -
          (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
        R *
            (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
              (refinedSixPoleKernel.function (1 / 2)).re) -
          5 *
            ((231 / 5000 : ℝ) * (6889 / 2700) +
              ((1839 / 1000 : ℝ) * (2 * Real.log R + 21 / 8) + 2) *
                  ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
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
      (refined_pair_paper_necessary hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
        hqK hrK hvq hvr hR hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
