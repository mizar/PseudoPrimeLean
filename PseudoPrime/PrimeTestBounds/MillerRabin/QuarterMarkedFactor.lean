/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.MixedTwoAdicLogBounds

/-! # Quarter-square bound from a marked prime factor -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd input with at least three distinct prime factors and a
marked local factor has a rejecting prime below the one-quarter bound. The marked-factor
estimate has coefficient at most one quarter. -/
theorem exists_prime_reject_quarter_local_factor {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card)
    (hlocal :
      (∃ r ∈ n.primeFactors, ∃ s ∈ n.primeFactors, padicValNat 2 (s - 1) < padicValNat 2 (r - 1)) ∨
        ∃ r ∈ n.primeFactors, ¬r - 1 ∣ n - 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hf, hb, _⟩ := exists_leastWitness_le_local_factor_coefficient hn ho hc hlocal hGRH
  have hcR : (3 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hc
  have hden : (16 : ℝ) ≤ ((n.primeFactors.card : ℝ) + 1) ^ 2 := by nlinarith only [hcR]
  have hcoef : (4 : ℝ) / ((n.primeFactors.card : ℝ) + 1) ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (by linarith only [hden])).2
    nlinarith only [hden]
  exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
