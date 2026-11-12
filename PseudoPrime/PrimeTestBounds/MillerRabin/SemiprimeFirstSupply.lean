/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount

/-! # Shared weighted semiprime candidate for the first supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a numerical lower bound for the weighted count of the first
prime supply yields a semiprime witness when the cutoff and envelope fit. -/
theorem exists_prime_reject_first_supply {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed19Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (19 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed19Primes
      primeSeed19Weights 19 budget primeSeed19Weight 10 (by norm_num only) primeSeed19_labels.1
      (fun r hr ↦ (prime_seed19_prime_supply r hr).1)
      (fun r hr ↦ (prime_seed19_prime_supply r hr).2) primeSeed19_labels.2.2
      prime_seed19_weight_bounds primeSeed19_labels.2.1 C hcount hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
