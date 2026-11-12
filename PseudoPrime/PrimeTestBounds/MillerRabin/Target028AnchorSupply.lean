/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSeedSupplies

/-! # Weighted semiprime supply with even-character anchors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A numerical lower bound for the supply through 43 gives a semiprime
witness when its cutoff and local envelope fit the target. -/
theorem exists_prime_reject_semiprime_seed43_197 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (H C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed43Weights H) {D X : ℝ} (hD : D ≤ Real.log (C : ℝ))
    (hB : (43 : ℝ) ≤ X) (hlocal : localFullEnvelope (max ((H : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact exists_prime_reject_semiprime_seed43 hn ho hp hq hpq hprod hGRH H C hcount hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
