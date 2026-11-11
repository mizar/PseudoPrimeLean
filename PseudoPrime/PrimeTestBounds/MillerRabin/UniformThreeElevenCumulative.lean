/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CoarseZeroCountNumerics
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenLow
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenMiddle
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenCount

/-! # Uniform three-elevenths cumulative bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the displayed Chebyshev lower bound on the middle radii,
every uniform Korselt triple with logarithm at most four million has a
rejecting prime within the three-elevenths cutoff. -/
theorem uniform_three_eleven_to4m {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hpsi :
      ∀ x : ℝ,
        ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ x →
          x ≤ ((52223 / 100000 : ℝ) * 4000000) ^ 2 →
          x - (1 / 12 : ℝ) * Real.sqrt x * Real.log x ^ 2 ≤ Chebyshev.psi x)
    (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h10300 : Real.log n ≤ 10300
  · exact uniform_three_eleven_to10300 hn ho hu hGRH h10300
  have hL : (10300 : ℝ) ≤ Real.log n := le_of_not_ge h10300
  let r : ℝ := (52223 / 100000 : ℝ) * Real.log n
  have hrL : (52223 / 100000 : ℝ) * 10300 ≤ r := by
    dsimp only [r]
    exact mul_le_mul_of_nonneg_left hL (by norm_num only)
  have hrU : r ≤ (52223 / 100000 : ℝ) * 4000000 := by
    dsimp only [r]
    exact mul_le_mul_of_nonneg_left hU (by norm_num only)
  have hr0 : 0 ≤ r := le_trans (by norm_num only) hrL
  have hXlo : ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (by norm_num only) hrL 2
  have hXhi : r ^ 2 ≤ ((52223 / 100000 : ℝ) * 4000000) ^ 2 := pow_le_pow_left₀ hr0 hrU 2
  have hp := hpsi (r ^ 2) hXlo hXhi
  rw [Real.sqrt_sq hr0] at hp
  exact uniform_three_eleven_middle_at hn ho hu hGRH hp hL hU

/-- Under GRH and the displayed coarse positive-height zero-count bound, a
uniform Korselt triple with logarithm at most four million has a rejecting
prime within the three-elevenths cutoff. The count supplies the Chebyshev
input only for the middle interval. -/
theorem uniform_three_eleven_count_to4m {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h10300 : Real.log n ≤ 10300
  · exact uniform_three_eleven_to10300 hn ho hu hGRH h10300
  · exact uniform_three_eleven_count_middle hn ho hu hGRH hQ (le_of_not_ge h10300) hU

/-- The same cumulative uniform bound follows if the coarse count is known
only at heights away from nontrivial zeta zeros. Right limits extend it to
closed zero ordinates, retaining their multiplicities. -/
theorem uniform_three_eleven_good_to4m {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
          |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
                (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
            Real.log t)
    (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    uniform_three_eleven_count_to4m hn ho hu hGRH
      (AnalyticNumberTheory.RiemannZeta.positiveZeroCount_log_of_good hQ) hU

/-- A good-height zero-count estimate with the stated `3/8` error budget
also yields the cumulative uniform three-elevenths bound through four
million. The count estimate remains an explicit additional hypothesis. -/
theorem uniform_three_eleven_budget_to4m {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
          |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
                (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
            (3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t))
    (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  exact
    uniform_three_eleven_count_to4m hn ho hu hGRH
      (AnalyticNumberTheory.RiemannZeta.positiveZeroCount_log_of_good_budget hQ) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
