/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.IndexedPrimeSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeTable

/-! # Semiprime witnesses from indexed nested prime supplies -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a distinct semiprime has a bounded rejecting prime when a
checked weighted table and indexed prime-count cutoffs satisfy the count and
local-envelope bounds. Each index may use a different certified cutoff and
weight; the first-prime labels turn them into a duplicate-free prime supply. -/
theorem exists_prime_reject_semiprime_indexed {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (M B budget N : ℕ) (b w : ℕ → ℕ)
    (d : ℝ) (hd : 0 < d) (hcount : ∀ i < M, i < (b i).primeCounting) (hbound : ∀ i < M, b i ≤ B)
    (hweight : ∀ i < M, Real.log (b i) ≤ (w i : ℝ) / d) (hpos : ∀ i < M, 0 < w i) (hN : budget ≤ N)
    (row : Array ℕ) (rows : List (Array ℕ))
    (hcheck : weightedPrimeTableCheck N ((List.range M).map w) (row :: rows) = true) {D X : ℝ}
    (hD : D ≤ Real.log (row.getD budget 0 : ℝ)) (hB : (B : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / d) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hprime := NumberTheory.firstPrimeLabels_prime M
  have hbounds := NumberTheory.firstPrimeLabels_indexed_bounds b w d hcount hbound hweight
  have hwpos : ∀ r ∈ NumberTheory.firstPrimeLabels M, 0 < NumberTheory.indexedPrimeWeight w r := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    simpa only [NumberTheory.indexedPrimeWeight, Nat.primeCounting'_nth_eq] using
      hpos i (List.mem_range.mp hi)
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH (NumberTheory.firstPrimeLabels M)
      ((List.range M).map w) B budget N (NumberTheory.indexedPrimeWeight w) d hd
      (NumberTheory.firstPrimeLabels_nodup M) hprime (fun r hr ↦ (hbounds r hr).1) hwpos
      (fun r hr ↦ (hbounds r hr).2) (NumberTheory.firstPrimeLabels_weights M w) hN row rows hcheck
      hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
