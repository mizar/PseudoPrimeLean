/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028PairSharp

/-! # Finite cutoff comparison for the uniform triple cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a uniform three-prime Korselt product under GRH, a lower bound on the
principal cutoff exceeding the explicit analytic error yields a prime Miller--Rabin
witness at most `X`. This is the contrapositive of the explicit pair-character gap. -/
theorem target028_finite_pair_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X : ℝ} (hX : 1000 ≤ X)
    (hgap :
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
          (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
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
      (target028_pair_gap_numeric hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK
        hrK hvq hvr hX hall)

end PseudoPrime.PrimeTestBounds.MillerRabin
