/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleLowCover
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030NonuniformRanges
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Low394

/-! # All-factor low bridge for the 0.30 target -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm in `[8,39.52]` has a prime
Miller–Rabin witness below the `3/10` cutoff. The existing range handles the
part through `39.4`; the uniform triple cell cover and nonuniform witness
handle the remaining interval. -/
theorem exists_prime_reject_03_log8_3952 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 988 / 25) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  by_cases hsmall : Real.log n ≤ (197 / 5 : ℝ)
  · exact exists_prime_reject_03_log8_to_394 hn ho hc hGRH hL hsmall
  · by_cases hu : UniformKorseltTriple n
    · exact uniformKorselt_reject_394_3952 hn ho hu hGRH (le_of_not_ge hsmall) hU
    · apply exists_prime_reject_03_nonuniform_ranges hn ho hc hu hGRH hL
      left
      linarith only [hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
