/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SignedPrimeProductTransfer

/-! # Signed semiprime cells for weighted prime families -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A weighted prime family reduces a semiprime witness to a local logarithmic
case. Membership supplies the supported-prime and budget conditions; the
caller supplies the cardinality estimate and the local witness. -/
theorem exists_prime_reject_weighted_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p * q) (S : Finset ℕ) (w : ℕ → ℕ) (H B : ℕ) (d : ℝ) (hd : 0 < d)
    (hwpos : ∀ r ∈ S, 1 ≤ w r) (hprime : ∀ r ∈ S, r.Prime) (hbound : ∀ r ∈ S, r ≤ B)
    (hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / d) {A D X : ℝ} (hA : Real.log 2 + (H : ℝ) / d ≤ A)
    (hD : D ≤ Real.log ((2 * (weightedPrimeFamily S w H).card : ℕ) : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hsub : ∀ T ∈ weightedPrimeFamily S w H, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).1
  have hcost : ∀ T ∈ weightedPrimeFamily S w H, (T.map w).sum ≤ H := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).2
  exact
    exists_prime_reject_signed_cell hn ho hp hq hprod S (weightedPrimeFamily S w H) B H w d hd hsub
      hprime hbound hw hcost hA hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
