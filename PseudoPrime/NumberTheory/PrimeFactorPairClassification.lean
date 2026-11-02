/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-! # Numbers with two prime factors counted with multiplicity -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- If `n > 1` has exactly two prime factors counted with multiplicity, it
is a product `p * q` of primes with `p ≤ q`. Extract the two entries of the
prime factor list and use its product identity; the equal case includes squares. -/
theorem exists_ordered_prime_pair_of_cardFactors_two {n : ℕ} (hn : 1 < n)
    (hcard : ArithmeticFunction.cardFactors n = 2) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ n = p * q := by
  have hl : n.primeFactorsList.length = 2 := by
    simpa only [ArithmeticFunction.cardFactors_apply] using hcard
  obtain ⟨p, q, hlist⟩ := List.length_eq_two.mp hl
  have hp : p.Prime :=
    Nat.prime_of_mem_primeFactorsList
      (by
        rw [hlist]
        exact List.mem_cons_self)
  have hq : q.Prime :=
    Nat.prime_of_mem_primeFactorsList
      (by
        rw [hlist]
        exact List.mem_cons_of_mem _ List.mem_cons_self)
  have hprod := Nat.prod_primeFactorsList (Nat.ne_zero_of_lt hn)
  rw [hlist] at hprod
  simp only [List.prod_cons, List.prod_nil, mul_one] at hprod
  rcases le_total p q with hpq | hqp
  · exact ⟨p, q, hp, hq, hpq, hprod.symm⟩
  · exact ⟨q, p, hq, hp, hqp, hprod.symm.trans (Nat.mul_comm p q)⟩

end PseudoPrime.NumberTheory
