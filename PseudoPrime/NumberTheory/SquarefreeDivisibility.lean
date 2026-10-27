/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree

/-! # Divisibility through squarefree numbers

Primewise divisibility conditions imply divisibility by a squarefree number.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/--
Inputs: a nonzero squarefree natural number `n` and a natural number `m` such
that every prime divisor of `n` divides `m`.

Claim: `n ∣ m`.

Proof: compare prime exponents; squarefreeness bounds each exponent in `n` by
one, while the primewise hypotheses provide the required exponents in `m`.

Role: lifts primewise divisibility statements to divisibility by a squarefree
modulus.
-/
theorem dvd_of_squarefree_prime_dvd {n m : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0)
    (h : ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∣ m) : n ∣ m := by
  by_cases hm0 : m = 0
  · simp only [hm0, dvd_zero]
  · apply (Nat.factorization_prime_le_iff_dvd hn0 hm0).mp
    intro p hp
    by_cases hpn : p ∣ n
    · rw [Nat.factorization_eq_one_of_squarefree hn hp hpn]
      exact (Nat.Prime.dvd_iff_one_le_factorization hp hm0).mp (h p hp hpn)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact Nat.zero_le _

/--
Inputs: a squarefree natural number `m` and a nonzero modulus `Q`.

Claim: `m` factors as a squarefree divisor of `Q` times a squarefree part
coprime to `Q`.

Proof: take the common part to be `gcd m Q`; squarefreeness passes to both
factors, and the quotient is coprime to `Q`.

Role: gives the arithmetic decomposition needed to compare restricted and
unrestricted squarefree reciprocal sums.
-/
theorem squarefree_coprime_factorization {m Q : ℕ} (hm : Squarefree m) (hQ : Q ≠ 0) :
    ∃ n d : ℕ, m = n * d ∧ Squarefree n ∧ Nat.Coprime n Q ∧ Squarefree d ∧ d ∣ Q := by
  let d : ℕ := Nat.gcd m Q
  let n : ℕ := m / d
  have hdvdm : d ∣ m := Nat.gcd_dvd_left m Q
  have hdvdQ : d ∣ Q := Nat.gcd_dvd_right m Q
  have hnfac : m = n * d := by simpa only [n, d] using (Nat.div_mul_cancel hdvdm).symm
  have hnsq : Squarefree n := by exact hm.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvdm)
  have hncop : Nat.Coprime n Q := by simpa only [n, d] using Nat.coprime_div_gcd_of_squarefree hm hQ
  have hdsq : Squarefree d := hm.squarefree_of_dvd hdvdm
  exact ⟨n, d, hnfac, hnsq, hncop, hdsq, hdvdQ⟩

end PseudoPrime.NumberTheory
