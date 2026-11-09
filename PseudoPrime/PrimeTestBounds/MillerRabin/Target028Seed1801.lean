/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareGroupedSupply

/-! # Reduced grouped prime supply through 1801 -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing supply through 1849 with its four largest labels removed. -/
def target028Seed1801Primes : List ℕ :=
  primeSeed1849Extra.drop 4 ++ primeSeed373Primes

/-- The remaining 205 extra labels retain their common cost 76. -/
def target028Seed1801Weights : List ℕ :=
  List.replicate 205 76 ++ primeSeed373Weights

/-- The reduced supply is duplicate-free, has positive weights, and its
ordered weight list is the grouped recurrence input. -/
theorem target028Seed1801_labels :
    target028Seed1801Primes.Nodup ∧
      target028Seed1801Primes.map primeSeed1849Weight = target028Seed1801Weights ∧
      ∀ p ∈ target028Seed1801Primes, 0 < primeSeed1849Weight p := by
  decide +kernel

/-- Every reduced label occurs in the original certified supply. -/
theorem target028Seed1801_subset : ∀ p ∈ target028Seed1801Primes, p ∈ primeSeed1849Primes := by
  intro p hp
  simp only [target028Seed1801Primes, primeSeed1849Primes, List.mem_append] at hp ⊢
  exact hp.imp List.mem_of_mem_drop id

/-- Every reduced label is prime and at most 1801. Primality follows from the
original supply; the smaller cutoff is a finite check. -/
theorem target028Seed1801_supply : ∀ p ∈ target028Seed1801Primes, p.Prime ∧ p ≤ 1801 := by
  have hbound : ∀ p ∈ target028Seed1801Primes, p ≤ 1801 := by decide +kernel
  intro p hp
  exact ⟨(primeSeed1849_prime_supply p (target028Seed1801_subset p hp)).1, hbound p hp⟩

/-- The grouped count with 205 extra labels extends the certified base row. -/
theorem target028Seed1801_count (A k : ℕ) (hA : A ≤ 500) :
    Nat.choose (205 + k) k * primeSeed373Row14.getD A 0 ≤
      weightedPrimeCount id target028Seed1801Weights (A + k * 76) := by
  have hb := primeSeed373_count_lower A hA
  have hg := weightedPrimeCount_group_lower 76 A 205 k primeSeed373Weights (by decide)
  exact (Nat.mul_le_mul_left (Nat.choose (205 + k) k) hb).trans hg

end PseudoPrime.PrimeTestBounds.MillerRabin
