/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TotalFactorWitnessBounds

/-! # Quarter-square bound for at least four prime factors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with at least four prime factors counted with
multiplicity has a rejecting prime below the one-quarter bound. The total-factor estimate
has coefficient at most one quarter. -/
theorem exists_prime_reject_quarter_four_factors {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hk : 4 ≤ ArithmeticFunction.cardFactors n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_cardFactors_log_sq hn ho hc hGRH
  have hkR : (4 : ℝ) ≤ ArithmeticFunction.cardFactors n := by exact_mod_cast hk
  have hden : (16 : ℝ) ≤ (ArithmeticFunction.cardFactors n : ℝ) ^ 2 := by nlinarith only [hkR]
  have hcoef : (4 : ℝ) / (ArithmeticFunction.cardFactors n : ℝ) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
