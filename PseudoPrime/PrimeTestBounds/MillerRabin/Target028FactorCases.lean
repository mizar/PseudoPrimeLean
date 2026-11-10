/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFactorCases
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # Factor-count cases with coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with at least four prime factors counted with
multiplicity has a rejecting prime below the 0.28 bound. The total-factor estimate
has coefficient at most one quarter. -/
theorem exists_prime_reject_028_four_factors {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_quarter_four_factors hn ho hc hk hGRH
  have hcoef : (1 / 4 : ℝ) ≤ 7 / 25 := by norm_num only
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

/-- Under GRH, a squarefree odd integer with exactly three distinct prime factors
has a rejecting prime below the 0.28 bound unless it is a uniform Korselt triple.
Failure of the exceptional conditions supplies a marked local factor. -/
theorem exists_prime_reject_028_nonuniform_three {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_quarter_nonuniform_three hn ho hsf hc hu hGRH
  have hcoef : (1 / 4 : ℝ) ≤ 7 / 25 := by norm_num only
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
