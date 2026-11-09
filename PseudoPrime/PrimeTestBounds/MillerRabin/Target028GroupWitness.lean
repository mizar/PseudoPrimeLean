/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount

/-! # Semiprime witnesses from grouped count certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A numerical lower bound for the grouped prime count through 1849 yields
a semiprime witness when its cutoff and local envelope fit the target. -/
theorem exists_prime_reject_semiprime_group {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (H C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed1849Weights H) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (1849 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((H : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed1849Primes
      primeSeed1849Weights 1849 H primeSeed1849Weight 10 (by norm_num only) primeSeed1849_labels.1
      (fun r hr ↦ (primeSeed1849_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed1849_prime_supply r hr).2) primeSeed1849_labels.2.2
      primeSeed1849_weight_bounds primeSeed1849_labels.2.1 C hcount hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
