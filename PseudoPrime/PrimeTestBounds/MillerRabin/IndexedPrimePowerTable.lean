/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.IndexedPrimeSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimePowerTable

/-! # Prime-power witnesses from indexed nested prime supplies -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An odd input divisible by an odd prime power has a bounded rejecting prime
when indexed prime-count cutoffs and a checked weighted table meet the budget
and count conditions. Each prime index may use its own cutoff and weight. -/
theorem exists_prime_reject_prime_pow_indexed {n p a : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 0 < a) (hdiv : p ^ a ∣ n) (M B budget N : ℕ) (b w : ℕ → ℕ) (d : ℝ)
    (hd : 0 < d) (hcount : ∀ i < M, i < (b i).primeCounting) (hbound : ∀ i < M, b i ≤ B)
    (hweight : ∀ i < M, Real.log (b i) ≤ (w i : ℝ) / d) (hpos : ∀ i < M, 0 < w i) (hN : budget ≤ N)
    (row : Array ℕ) (rows : List (Array ℕ))
    (hcheck : weightedPrimeTableCheck N ((List.range M).map w) (row :: rows) = true)
    (hbudget : (budget : ℝ) / d < Real.log ((p ^ a : ℕ) : ℝ))
    (hfamily : p - 1 < row.getD budget 0) :
    ∃ r : ℕ, r.Prime ∧ r ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hprime := NumberTheory.firstPrimeLabels_prime M
  have hbounds := NumberTheory.firstPrimeLabels_indexed_bounds b w d hcount hbound hweight
  have hwpos : ∀ r ∈ NumberTheory.firstPrimeLabels M, 0 < NumberTheory.indexedPrimeWeight w r := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    simpa only [NumberTheory.indexedPrimeWeight, Nat.primeCounting'_nth_eq] using
      hpos i (List.mem_range.mp hi)
  exact
    exists_prime_reject_prime_pow_table hn ho hp hp2 ha hdiv (NumberTheory.firstPrimeLabels M)
      ((List.range M).map w) B budget N (NumberTheory.indexedPrimeWeight w) d hd
      (NumberTheory.firstPrimeLabels_nodup M) hprime (fun r hr ↦ (hbounds r hr).1) hwpos
      (fun r hr ↦ (hbounds r hr).2) (NumberTheory.firstPrimeLabels_weights M w) hN row rows hcheck
      hbudget hfamily

end PseudoPrime.PrimeTestBounds.MillerRabin
