/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterElevenCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell

/-! # Signed semiprime cells from the eleven-prime count table -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked eleven-prime count reduces a semiprime witness to a local
logarithmic case. The budget remains variable so that individual cells can
reuse the same weighted-family construction without expanding it again. -/
theorem quarter_eleven_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hprod : n = p * q) (H B : ℕ) (hH : H ≤ 73) (h31 : 31 ≤ B) {A D X : ℝ}
    (hA : Real.log 2 + (H : ℝ) / 10 ≤ A)
    (hD : D ≤ Real.log ((2 * quarterElevenRow.getD H 0 : ℕ) : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028ElevenPrimes.toFinset
  let w := target028ElevenWeight
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target028Eleven_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ B := fun r hr ↦
    ((target028Eleven_supply r (List.mem_toFinset.mp hr)).2.1).trans h31
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    (target028Eleven_supply r (List.mem_toFinset.mp hr)).2.2
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Eleven_labels.2.2 r (List.mem_toFinset.mp hr)
  have hDF : D ≤ Real.log ((2 * (weightedPrimeFamily S w H).card : ℕ) : ℝ) := by
    rw [quarter_eleven_family_card H hH]
    exact hD
  exact
    exists_prime_reject_weighted_cell hn ho hp hq hprod S w H B 10 (by norm_num only) hwpos hprime
      hbound hw hA hDF hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
