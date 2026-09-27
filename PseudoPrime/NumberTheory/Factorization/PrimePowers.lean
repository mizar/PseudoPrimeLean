/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Aggregation of prime factor lists
-/

namespace PseudoPrime.NumberTheory.Factorization

/-- Group a prime-factor list by distinct prime, storing each prime's occurrence count. -/
def aggregatePrimeFactorList (factors : List ℕ) : List (ℕ × ℕ) :=
  factors.dedup.map (fun q => (q, factors.count q))

/-- Aggregating repeated entries into prime powers preserves the list product. -/
theorem aggregatePrimeFactorList_product (factors : List ℕ) :
    ((aggregatePrimeFactorList factors).map (fun qe => qe.1 ^ qe.2)).prod = factors.prod := by
  dsimp only [aggregatePrimeFactorList]
  simp only [List.map_map, Function.comp_def]
  rw [← List.prod_toFinset (fun q => q ^ factors.count q) (List.nodup_dedup factors)]
  have hset : factors.dedup.toFinset = factors.toFinset := by
    ext q
    simp only [List.toFinset_dedup, List.mem_toFinset]
  rw [hset, ← Finset.prod_list_count]

end PseudoPrime.NumberTheory.Factorization
