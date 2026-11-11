/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Count197
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeTable
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeCoreSupplies

/-! # Weighted semiprime supply with even-character anchors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked table through budget 197 supplies a semiprime witness using
primes at most 43 whenever the count and local envelope fit the target. -/
theorem exists_prime_reject_semiprime_seed43_197 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (H : ℕ) (hH : H ≤ 197) {D X : ℝ}
    (hD : D ≤ Real.log (primeSeed43Row197.getD H 0 : ℝ)) (hB : (43 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((H : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed43Primes
      primeSeed43Weights 43 H 197 primeSeed43Weight 10 (by norm_num only) primeSeed43_labels.1
      (fun r hr ↦ (primeSeed43_prime_supply r hr).1) (fun r hr ↦ (primeSeed43_prime_supply r hr).2)
      primeSeed43_labels.2.2 primeSeed43_weight_bounds primeSeed43_labels.2.1 hH primeSeed43Row197
      primeSeed43Tail197 primeSeed43Table197_checked hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
