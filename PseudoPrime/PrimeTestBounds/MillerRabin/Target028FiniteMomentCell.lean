/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FinitePairMoments

/-! # Uniform-triple finite-cell interface -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a certified finite principal gap at an upper logarithmic endpoint
yields a 0.28 rejecting prime throughout the cell. The conductor coefficient is
nonnegative, so the upper endpoint bounds every input in the interval. -/
theorem target028_finite_moment_witness {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X U : ℝ} (hX : 252 ≤ X)
    (hU : Real.log n ≤ U) (hcut : X ≤ (7 / 25 : ℝ) * Real.log n ^ 2)
    (hgap :
      (2 * U) *
              (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
                X ^ (-(27 / 25 : ℝ)) *
                ((21 / 8 : ℝ) + Real.log X) ^ 5) +
            (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
            target028ReflectedMomentUpper X +
            (3 / 8 : ℝ) * U -
          (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
        4 *
            (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
              (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
          (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
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
          target028ReflectedMomentUpper X +
          (3 / 8 : ℝ) * Real.log n -
        (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 ≤
      4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
    linarith only [hm, hU, hgap']
  obtain ⟨l, hl, hlX, hf⟩ :=
    target028_finite_pair_moment252 hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr hX hcert
  exact ⟨l, hl, hlX.trans hcut, hf⟩

/-- The explicit upper budget for a finite uniform-triple cell. It combines
the conductor, Gamma, reflected Euler and zero-mass terms with the upper bound
for the full principal sum; the cell's finite principal sum is compared to it. -/
noncomputable def target028MomentBudget (X U : ℝ) : ℝ :=
  (2 * U) *
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
            X ^ (-(27 / 25 : ℝ)) *
            ((21 / 8 : ℝ) + Real.log X) ^ 5) +
        (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        target028ReflectedMomentUpper X +
        (3 / 8 : ℝ) * U -
      (547 / 100 : ℝ) * (27 / 25 : ℝ) ^ 5 +
    Real.sqrt X * (refinedSixPoleKernel.function (1 / 2)).re +
    ((231 / 5000 : ℝ) * ((203 / 1000) * (27 / 25 : ℝ) ^ 5) +
      ((1839 / 1000 : ℝ) * (Real.log X + 21 / 8) + 2) * ((251 / 500 : ℝ) * (27 / 25 : ℝ) ^ 5) /
        Real.sqrt X)

/-- A lower bound for the finite principal sum that exceeds the explicit
cell budget gives the 0.28 witness. The full principal sum is eliminated using
the sharp RH error estimate, leaving a finite certificate for each cutoff. -/
theorem target028_finite_moment_of_partial {n p q r : ℕ} [NeZero n] [NeZero p] [NeZero q] [NeZero r]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hsq : Squarefree n) (hnprod : n = p * q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 1 < n) (ho : Odd n)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n)
    (hpqn : p * q ∣ n) (hprn : p * r ∣ n) (hqrn : q * r ∣ n) (hpK : p - 1 ∣ n - 1)
    (hqK : q - 1 ∣ n - 1) (hrK : r - 1 ∣ n - 1)
    (hvq : padicValNat 2 (q - 1) = padicValNat 2 (p - 1))
    (hvr : padicValNat 2 (r - 1) = padicValNat 2 (p - 1)) {X U S : ℝ} (hX : 252 ≤ X)
    (hU : Real.log n ≤ U) (hcut : X ≤ (7 / 25 : ℝ) * Real.log n ^ 2)
    (hS :
      S ≤
        ∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re)
    (hcert : target028MomentBudget X U ≤ 4 * S) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hX1 : (1 : ℝ) ≤ X := by linarith only [hX]
  have hfull := (abs_le.mp (target028_full_principal_error hGRH.riemann hX1)).2
  apply
    target028_finite_moment_witness hsq hnprod hGRH hn ho hp hq hr hpn hqn hrn hpqn hprn hqrn hpK
      hqK hrK hvq hvr hX hU hcut
  dsimp only [target028MomentBudget] at hcert
  linarith only [hfull, hS, hcert]

end PseudoPrime.PrimeTestBounds.MillerRabin
