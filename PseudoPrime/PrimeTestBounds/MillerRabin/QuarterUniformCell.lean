/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformPairGap

/-! # Quarter-square criterion for a uniform triple on a logarithmic cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a certified finite principal gap at an upper logarithmic endpoint
yields a quarter-square rejecting prime throughout the cell. The conductor coefficient is
nonnegative, so the upper endpoint bounds every input in the interval. -/
theorem quarter_uniform_cell {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X U H : ℝ} (hX : 1 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (hU : Real.log n ≤ U)
    (hcut : X ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hgap :
      (2 * U) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                X ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log X) ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
            H +
            (3 / 8 : ℝ) * U +
            (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
          4 * ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
        4 *
            (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
              (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
          (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hX1 : (1 : ℝ) ≤ X := by linarith only [hX]
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hc :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * X ^ (-(27 / 25 : ℝ)) *
        ((21 / 8 : ℝ) + Real.log X) ^ 5) := by
    positivity
  have hm := mul_le_mul_of_nonneg_right (show 2 * Real.log n ≤ 2 * U by linarith only [hU]) hc
  have hgap' := hgap
  have hcert :
    (2 * Real.log n) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              X ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log X) ^ 5) +
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
          H +
          (3 / 8 : ℝ) * Real.log n +
          (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
        4 * ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k ≤
      4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
    linarith only [hm, hU, hgap']
  obtain ⟨l, hl, hlX, hf⟩ :=
    quarter_uniform_pair_witness hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK
      hrK hvq hvr hX hH hcert
  exact ⟨l, hl, hlX.trans hcut, hf⟩

/-- The numerical budget for a uniform-triple cell with a lower Euler prefix
bound `P` and an upper bound `F` for the full principal series. -/
noncomputable def quarterUniformBudget (X U P F H : ℝ) : ℝ :=
  (2 * U) *
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
            X ^ (-(27 / 25 : ℝ)) *
            ((21 / 8 : ℝ) + Real.log X) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        H +
        (3 / 8 : ℝ) * U +
        (65 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 -
      4 * P +
    F

/-- A lower finite principal bound, a lower Euler prefix bound and an upper
full principal bound give the quarter-square witness when their rational
cell budget fits. The input bounds may be established independently. -/
theorem quarter_uniform_cell_of_bounds {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X U S P F H : ℝ} (hX : 1 ≤ X)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) X ≤ H) (hU : Real.log n ≤ U)
    (hcut : X ≤ (1 / 4 : ℝ) * Real.log n ^ 2)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hP : P ≤ ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k * refinedSixEulerWeight k)
    (hF : (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤ F)
    (hcert : quarterUniformBudget X U P F H ≤ 4 * S) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  apply
    quarter_uniform_cell hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK hqK hrK hvq
      hvr hX hH hU hcut
  dsimp only [quarterUniformBudget] at hcert
  linarith only [hF, hS, hP, hcert]

end PseudoPrime.PrimeTestBounds.MillerRabin
