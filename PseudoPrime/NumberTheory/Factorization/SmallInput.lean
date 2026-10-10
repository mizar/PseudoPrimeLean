/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorization.Defs

/-! # Bounded trial-division factorizations -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Factorization.SmallInput

/-- Factor a positive input within the selected limit using repeated smallest factors.
Return an ascending list with multiplicity; one has the empty factorization, zero has none.
The limit is checked before factoring and is not a wall-clock guarantee. -/
def factorUpTo (limit n : ℕ) : Option (List ℕ) :=
  if 0 < n ∧ n ≤ limit then some n.primeFactorsList else none

/-- A factorization is returned exactly for a positive in-range input and equals the
canonical ascending prime-factor list. This preserves the zero/one boundary distinction. -/
theorem factorUpTo_eq_some_iff {limit n : ℕ} {factors : List ℕ} :
    factorUpTo limit n = some factors ↔ 0 < n ∧ n ≤ limit ∧ factors = n.primeFactorsList := by
  unfold factorUpTo
  split
  · rename_i h
    simp only [Option.some.injEq, h.1, h.2, true_and]
    exact eq_comm
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact False.elim (h ⟨he.1, he.2.1⟩)

/-- Returned factors are prime, sorted and multiply to the original input.
Their multiplicities equal Nat.factorization, allowing prime-power consumers to reuse them. -/
theorem factorUpTo_spec {limit n : ℕ} {factors : List ℕ} (h : factorUpTo limit n = some factors) :
    factors.prod = n ∧
      (∀ p ∈ factors, Nat.Prime p) ∧
      List.SortedLE factors ∧ ∀ p, factors.count p = n.factorization p := by
  obtain ⟨hn, _, rfl⟩ := factorUpTo_eq_some_iff.mp h
  exact
    ⟨Nat.prod_primeFactorsList (Nat.ne_of_gt hn), fun _ hp ↦ Nat.prime_of_mem_primeFactorsList hp,
      Nat.primeFactorsList_sorted n, fun _ ↦ Nat.primeFactorsList_count_eq⟩

/-- Factorization is unavailable exactly for zero or inputs above the limit. -/
theorem factorUpTo_eq_none_iff {limit n : ℕ} :
    factorUpTo limit n = none ↔ ¬(0 < n ∧ n ≤ limit) := by
  unfold factorUpTo
  split
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact False.elim (he h)
  · rename_i h
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

end PseudoPrime.NumberTheory.Factorization.SmallInput
