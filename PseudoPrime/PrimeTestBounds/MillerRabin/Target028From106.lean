/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028LargeIndex
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ResidualEndpoint

/-! # Global factor cases above logarithmic scale 106 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm at least 106 has a rejecting
prime within the 0.28 cutoff. Separate uniform Korselt triples from the existing
nonuniform finite-index and high-index branches. -/
theorem exists_prime_reject_028_from106 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (106 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hu : UniformKorseltTriple n
  · exact target028_uniform_high_witness hn ho hu hGRH (by linarith only [hL])
  · exact exists_prime_reject_028_nonuniform106 hn ho hc hGRH hL hu

end PseudoPrime.PrimeTestBounds.MillerRabin
