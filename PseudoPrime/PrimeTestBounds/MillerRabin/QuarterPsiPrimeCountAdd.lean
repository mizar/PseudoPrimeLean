/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev

/-! # Additivity of prime counts on adjacent intervals -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The number of primes in `(a, c]` is the sum of the counts in `(a, b]` and
`(b, c]` when `a ≤ b ≤ c`. The adjacent intervals are disjoint. -/
theorem prime_count_Ioc_add (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    letI : ∀ n : ℕ, Decidable n.Prime := Nat.decidablePrime'
    ((Finset.Ioc a c).filter Nat.Prime).card =
      ((Finset.Ioc a b).filter Nat.Prime).card + ((Finset.Ioc b c).filter Nat.Prime).card := by
  let : ∀ n : ℕ, Decidable n.Prime := Nat.decidablePrime'
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbc, Finset.filter_union]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1).2
  have hy' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1).1
  exact (Nat.not_lt_of_ge hx') hy'

end PseudoPrime.PrimeTestBounds.MillerRabin
