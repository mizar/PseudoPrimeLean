/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factors
public import Mathlib.Algebra.BigOperators.Ring.List

/-! # Prime factors detecting a nontrivial power -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For a positive natural a whose image has E-th power different from one,
some prime at most a has the same property in any commutative semiring.
Otherwise all prime factors, hence their product a, have power one.
This turns an integer Fermat-quotient witness into a prime witness. -/
theorem exists_prime_le_of_nat_power_ne_one {R : Type*} [CommSemiring R] {a E : ℕ} (ha : 0 < a)
    (hbad : (a : R) ^ E ≠ 1) : ∃ r : ℕ, r.Prime ∧ r ≤ a ∧ (r : R) ^ E ≠ 1 := by
  classical
  have hprod : ∀ l : List ℕ, (∀ r ∈ l, (r : R) ^ E = 1) → (l.prod : R) ^ E = 1 := by
    intro l
    induction l with
    | nil =>
      intro _
      simp only [List.prod_nil, Nat.cast_one, one_pow]
    | cons r l ih =>
      intro h
      rw [List.prod_cons, Nat.cast_mul, mul_pow, h r (List.mem_cons_self),
        ih (fun s hs ↦ h s (List.mem_cons_of_mem r hs)), one_mul]
  by_contra hn
  apply hbad
  rw [← Nat.prod_primeFactorsList ha.ne']
  apply hprod
  intro r hr
  by_contra hf
  exact
    hn
      ⟨r, Nat.prime_of_mem_primeFactorsList hr,
        Nat.le_of_dvd ha (Nat.dvd_of_mem_primeFactorsList hr), hf⟩

end PseudoPrime.NumberTheory
