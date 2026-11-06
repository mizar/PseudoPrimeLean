/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.NestedPrimeSupply
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Indexed prime labels for nested weighted supplies -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The first `M` primes as a list indexed from zero. The order records which
prime-count cutoff applies to each label in a nested supply. -/
noncomputable def firstPrimeLabels (M : ℕ) : List ℕ :=
  (List.range M).map (Nat.nth Nat.Prime)

/-- Give a prime the weight assigned to its zero-based prime index. The index
is its strict prime-counting value, so this definition recovers an arbitrary
indexed weight list on the ordered prime labels. -/
def indexedPrimeWeight (w : ℕ → ℕ) (p : ℕ) : ℕ :=
  w p.primeCounting'

/-- The first-prime labels have no duplicates because the nth-prime function
is strictly increasing. This permits their use as distinct product labels. -/
theorem firstPrimeLabels_nodup (M : ℕ) : (firstPrimeLabels M).Nodup := by
  apply (List.nodup_map_iff_inj_on List.nodup_range).2
  intro x hx y hy he
  exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective he

/-- Every member of the indexed prime-label list is prime. -/
theorem firstPrimeLabels_prime (M : ℕ) : ∀ p ∈ firstPrimeLabels M, p.Prime := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact Nat.prime_nth_prime i

/-- Mapping indexed prime weights over the first-prime labels gives exactly
the weights indexed from zero through `M - 1`. Equal weights retain separate
prime labels, which is needed for weighted product counting. -/
theorem firstPrimeLabels_weights (M : ℕ) (w : ℕ → ℕ) :
    (firstPrimeLabels M).map (indexedPrimeWeight w) = (List.range M).map w := by
  rw [firstPrimeLabels, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, indexedPrimeWeight, Nat.primeCounting'_nth_eq]

/-- A lower bound of `M` on the prime count through `B` puts every one of the
first `M` prime labels at or below `B`. -/
theorem firstPrimeLabels_le {M B : ℕ} (hcount : M ≤ B.primeCounting) :
    ∀ p ∈ firstPrimeLabels M, p ≤ B := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hiM := List.mem_range.mp hi
  have hiB : i < Nat.count Nat.Prime (B + 1) := by
    change i < B.primeCounting
    exact hiM.trans_le hcount
  exact Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hiB)

/-- Given a certified cutoff and weight for every index below `M`, each prime
label lies below the global cutoff and its logarithm is bounded by its assigned
weight divided by `d`. Prime-count lower bounds select the relevant cutoff. -/
theorem firstPrimeLabels_indexed_bounds {M B : ℕ} (b w : ℕ → ℕ) (d : ℝ)
    (hcount : ∀ i < M, i < (b i).primeCounting) (hbound : ∀ i < M, b i ≤ B)
    (hweight : ∀ i < M, Real.log (b i) ≤ (w i : ℝ) / d) :
    ∀ p ∈ firstPrimeLabels M, p ≤ B ∧ Real.log p ≤ (indexedPrimeWeight w p : ℝ) / d := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have hiM := List.mem_range.mp hi
  have hiB : i < Nat.count Nat.Prime (b i + 1) := by
    change i < (b i).primeCounting
    exact hcount i hiM
  have hpB : Nat.nth Nat.Prime i ≤ b i := Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hiB)
  have hpLog := Real.log_le_log (Nat.cast_pos.mpr (Nat.prime_nth_prime i).pos) (Nat.cast_le.mpr hpB)
  refine ⟨hpB.trans (hbound i hiM), ?_⟩
  simpa only [indexedPrimeWeight, Nat.primeCounting'_nth_eq] using hpLog.trans (hweight i hiM)

end PseudoPrime.NumberTheory
