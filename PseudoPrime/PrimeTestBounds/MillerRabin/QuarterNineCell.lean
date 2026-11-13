/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNineCount90
public import PseudoPrime.PrimeTestBounds.MillerRabin.SignedWeightedCell

/-! # Signed semiprime cells from the nine-prime count table -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked nine-prime count reduces a semiprime witness to a local
logarithmic case. The budget remains variable so that individual cells can
reuse the same weighted-family construction without expanding it again. -/
private theorem quarter_nine_cell {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hprod : n = p * q) (H B : ℕ) (hH : H ≤ 90) (h23 : 23 ≤ B) {A D X : ℝ}
    (hA : Real.log 2 + (H : ℝ) / 10 ≤ A)
    (hD : D ≤ Real.log ((2 * quarterNine90Row.getD H 0 : ℕ) : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028NinePrimes.toFinset
  let w := target028NineWeight
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (target028Nine_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ B := fun r hr ↦
    ((target028Nine_supply r (List.mem_toFinset.mp hr)).2.1).trans h23
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    (target028Nine_supply r (List.mem_toFinset.mp hr)).2.2
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Nine_labels.2.2 r (List.mem_toFinset.mp hr)
  have hDF : D ≤ Real.log ((2 * (weightedPrimeFamily S w H).card : ℕ) : ℝ) := by
    rw [quarter_nine90_family_card H hH]
    exact hD
  exact
    exists_prime_reject_weighted_cell hn ho hp hq hprod S w H B 10 (by norm_num only) hwpos hprime
      hbound hw hA hDF hB hlocal

/-- For budget 60, the checked nine-prime family gives the stated semiprime
witness whenever the local logarithmic reduction holds. The integer 390 is
its certified signed-family count. -/
theorem quarter_nine_cell_60 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hprod : n = p * q) (B : ℕ) (hB0 : 23 ≤ B) {A D X : ℝ} (hA : Real.log 2 + (60 : ℝ) / 10 ≤ A)
    (hD : D ≤ Real.log (390 : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact quarter_nine_cell hn ho hp hq hprod 60 B (by decide) hB0 hA hD hB hlocal

/-- For budget 67, the checked nine-prime family gives the stated semiprime
witness whenever the local logarithmic reduction holds. The integer 614 is
its certified signed-family count. -/
theorem quarter_nine_cell_67 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hprod : n = p * q) (B : ℕ) (hB0 : 23 ≤ B) {A D X : ℝ} (hA : Real.log 2 + (67 : ℝ) / 10 ≤ A)
    (hD : D ≤ Real.log (614 : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact quarter_nine_cell hn ho hp hq hprod 67 B (by decide) hB0 hA hD hB hlocal

/-- For budget 70, the checked nine-prime family gives the stated semiprime
witness whenever the local logarithmic reduction holds. The integer 736 is
its certified signed-family count. -/
theorem quarter_nine_cell_70 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hprod : n = p * q) (B : ℕ) (hB0 : 23 ≤ B) {A D X : ℝ} (hA : Real.log 2 + (70 : ℝ) / 10 ≤ A)
    (hD : D ≤ Real.log (736 : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact quarter_nine_cell hn ho hp hq hprod 70 B (by decide) hB0 hA hD hB hlocal

/-- For budget 72, the checked nine-prime family gives the stated semiprime
witness whenever the local logarithmic reduction holds. The integer 836 is
its certified signed-family count. -/
theorem quarter_nine_cell_72 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hprod : n = p * q) (B : ℕ) (hB0 : 23 ≤ B) {A D X : ℝ} (hA : Real.log 2 + (72 : ℝ) / 10 ≤ A)
    (hD : D ≤ Real.log (836 : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal :
      Real.log q ≤ max A (Real.log n - D) →
        ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact quarter_nine_cell hn ho hp hq hprod 72 B (by decide) hB0 hA hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
