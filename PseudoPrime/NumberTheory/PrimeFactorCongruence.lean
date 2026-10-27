/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.ModEq

/-! # Congruence one inherited from all prime divisors -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- For positive m,n, a common divisor of m-1 and n-1 divides m*n-1.
Multiplication of residue-one congruences proves the claim. This is the product
step when transferring local congruences through a prime factorization. -/
private theorem dvd_product_sub_one {m n k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hkm : k ∣ m - 1)
    (hkn : k ∣ n - 1) : k ∣ m * n - 1 := by
  have h := ((Nat.modEq_iff_dvd' hm).mpr hkm).mul ((Nat.modEq_iff_dvd' hn).mpr hkn)
  rw [one_mul] at h
  exact h.dvd'

/-- For nonzero n, if every prime divisor is congruent to one modulo k, then
n is congruent to one modulo k. Induct on multiplication by primes and combine
the two residue-one congruences. This transfers a minimum local two-adic
divisor to n-1 without assuming one prime's full p-1 divides n-1. -/
theorem dvd_sub_one_of_forall_prime_dvd {n k : ℕ} (hn : n ≠ 0)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n → k ∣ p - 1) : k ∣ n - 1 := by
  revert hn hprime
  induction n using Nat.recOnMul with
  | zero =>
    intro hn _
    exact (hn rfl).elim
  | one =>
    intro _ _
    exact dvd_zero k
  | prime p hp =>
    intro _ hprime
    exact hprime p hp dvd_rfl
  | mul m n ihm ihn =>
    intro hne hprime
    have hm : m ≠ 0 := (mul_ne_zero_iff.mp hne).1
    have hn : n ≠ 0 := (mul_ne_zero_iff.mp hne).2
    apply dvd_product_sub_one (Nat.one_le_iff_ne_zero.mpr hm) (Nat.one_le_iff_ne_zero.mpr hn)
    · exact ihm hm (fun p hp hd ↦ hprime p hp (hd.trans (dvd_mul_right m n)))
    · exact ihn hn (fun p hp hd ↦ hprime p hp (hd.trans (dvd_mul_left n m)))

end PseudoPrime.NumberTheory
