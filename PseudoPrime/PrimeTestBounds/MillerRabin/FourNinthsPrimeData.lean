/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeTable

/-! # Prime supply for the low four-ninths certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the zero-indexed `i`th prime is at most `B`, at least `i + 1` primes
are at most `B`. Reuse the existing prime indexing and the count of primes
through an indexed prime; this supplies low cells without re-enumeration. -/
theorem primeCount_ge_of_index {i B : ℕ} (h : NumberTheory.primeByIndex i ≤ B) :
    i + 1 ≤ B.primeCounting := by
  have hcount := Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime i
  have hle : Nat.count Nat.Prime (NumberTheory.primeByIndex i + 1) ≤ Nat.count Nat.Prime (B + 1) :=
    Nat.count_monotone Nat.Prime (Nat.add_le_add_right h 1)
  change Nat.count Nat.Prime (Nat.nth Nat.Prime i + 1) = i + 1 at hcount
  rw [← NumberTheory.primeByIndex] at hcount
  change i + 1 ≤ Nat.count Nat.Prime (B + 1)
  exact hcount.symm ▸ hle

/-- There are at least 185 primes at most 1103. Reuse the certified count of
the first 163 primes through 967, then certify the 22 explicitly listed
additional primes. Their disjoint union lies among the primes up to 1103. -/
theorem primeCount_1103_ge_185 : 185 ≤ (1103 : ℕ).primeCounting := by
  let E : Finset ℕ :=
    {971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033,
    1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103}
  have hecard : E.card = 22 := by decide +kernel
  have helow : ∀ p ∈ E, 967 < p := by decide +kernel
  have heprime : ∀ p ∈ E, p.Prime ∧ p ≤ 1103 := by decide +kernel
  have hbase : (967 : ℕ).primesLE.card = 163 := by
    rw [Nat.primesLE_card_eq_primeCounting]
    change Nat.count Nat.Prime (967 + 1) = 163
    rw [Nat.count_succ, NumberTheory.count_prime_at_162]
    norm_num only [ite_true]
  have hdis : Disjoint (967 : ℕ).primesLE E := by
    apply Finset.disjoint_left.mpr
    intro p hp hpe
    exact Nat.not_lt_of_ge (Nat.mem_primesLE.mp hp).1 (helow p hpe)
  have hsub : (967 : ℕ).primesLE ∪ E ⊆ (1103 : ℕ).primesLE := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨hle, hpr⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨hle.trans (by norm_num only), hpr⟩
    · exact Nat.mem_primesLE.mpr ⟨(heprime p hp).2, (heprime p hp).1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, hbase, hecard,
    Nat.primesLE_card_eq_primeCounting] at hcard
  exact hcard

end PseudoPrime.PrimeTestBounds.MillerRabin
