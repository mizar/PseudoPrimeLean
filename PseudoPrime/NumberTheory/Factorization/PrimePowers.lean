/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Aggregation of prime factor lists
-/

@[expose] public section

namespace PseudoPrime.NumberTheory.Factorization

/-- Group a natural-number list by distinct entry, storing each entry's occurrence count.
No primality hypothesis is required. Applied to a certified prime-factor list, the result supplies
the prime/exponent pairs expected by prime-power certificate consumers. -/
def aggregatePrimeFactorList (factors : List ℕ) : List (ℕ × ℕ) :=
  factors.dedup.map (fun q => (q, factors.count q))

/-- Aggregating repeated entries into powers preserves the product of any natural-number list.
The proof rewrites the deduplicated list as a finite set and uses the product-by-multiplicity
identity, so certified prime-factor lists can be converted without changing their represented
input. -/
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
