/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed43Count197
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime81
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EvenEnvelope

/-! # Weighted semiprime supply with even-character anchors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked table through budget 197 supplies a semiprime witness using
primes at most 43 whenever the count and local envelope fit the target. -/
theorem exists_prime_reject_semiprime_seed43_197 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (H : ℕ) (hH : H ≤ 197) {D X : ℝ}
    (hD : D ≤ Real.log (target030Seed43Row197.getD H 0 : ℝ)) (hB : (43 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((H : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed43Primes
      target030Seed43Weights 43 H 197 target030Seed43Weight 10 (by norm_num only)
      target030Seed43_labels.1 (fun r hr ↦ (target030Seed43_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed43_prime_supply r hr).2) target030Seed43_labels.2.2
      target030Seed43_weight_bounds target030Seed43_labels.2.1 hH target030Seed43Row197
      target030Seed43Tail197 target030Seed43Table197_checked hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
