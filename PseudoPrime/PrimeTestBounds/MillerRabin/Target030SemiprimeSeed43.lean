/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed43
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeTable
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Semiprime1217

/-! # Semiprime witnesses from the prime supply through 43 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the checked supply through 43 yields a distinct-semiprime
witness at any budget through 77 when the count and local envelope fit the
target. The generic table theorem transfers the count directly to the kernel. -/
theorem exists_prime_reject_semiprime_seed43 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 77)
    {D X : ℝ} (hD : D ≤ Real.log (target030Seed43Row.getD budget 0 : ℝ)) (hB : (43 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH target030Seed43Primes
      target030Seed43Weights 43 budget 77 target030Seed43Weight 10 (by norm_num only)
      target030Seed43_labels.1 (fun r hr ↦ (target030Seed43_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed43_prime_supply r hr).2) target030Seed43_labels.2.2
      target030Seed43_weight_bounds target030Seed43_labels.2.1 hN target030Seed43Row
      target030Seed43Tail target030Seed43_checked hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
