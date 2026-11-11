/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevSquareLog
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenMiddle

/-! # Uniform three-elevenths bounds from coarse zero counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH and the displayed coarse zero-count estimate, a uniform
Korselt triple with logarithm in `[10300, 4000000]` has a rejecting prime
within the three-elevenths cutoff. The count yields the needed Chebyshev
bound at the radius selected for that input. -/
theorem uniform_three_eleven_count_middle {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |AnalyticNumberTheory.RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hL : (10300 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 4000000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r : ℝ := (52223 / 100000 : ℝ) * Real.log n
  have hrL : (52223 / 100000 : ℝ) * 10300 ≤ r := by
    dsimp only [r]
    exact mul_le_mul_of_nonneg_left hL (by norm_num only)
  have hr0 : 0 ≤ r := le_trans (by norm_num only) hrL
  have hXlo : ((52223 / 100000 : ℝ) * 10300) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (by norm_num only) hrL 2
  have hbase : (25000000 : ℝ) ≤ ((52223 / 100000 : ℝ) * 10300) ^ 2 := by norm_num only
  have hp :=
    AnalyticNumberTheory.RiemannZeta.psi_lower_square_coarse hGRH.riemann (hbase.trans hXlo) hQ
  rw [Real.sqrt_sq hr0] at hp
  exact uniform_three_eleven_middle_at hn ho hu hGRH hp hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
