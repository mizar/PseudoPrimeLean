/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# Certificates for a smallest-prime-factor table

Separate the supplied finite table from its correctness proof. Divisibility and
bounds on the multiples of diagonal candidates imply equality with Nat.minFac.
A checked table can share prime-membership proofs across finite residue witnesses.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Correctness conditions for a supplied smallest-prime-factor table on [2, bound].
Every stored factor is at least two and divides its index. For a diagonal candidate p,
all its multiples starting at p squared must store a factor at most p.
The conditions imply that the table agrees with Nat.minFac; no independent primality
test for each diagonal entry is required. Values outside the certified range are irrelevant.
A finite sieve checker can provide these conditions for shared prime-membership proofs. -/
structure SmallestPrimeFactorTableCertificate (bound : ℕ) (factor : ℕ → ℕ) : Prop where
  /-- Every certified factor is at least two. -/
  two_le_factor : ∀ n, 2 ≤ n → n ≤ bound → 2 ≤ factor n
  /-- Every certified factor divides its index. -/
  factor_dvd : ∀ n, 2 ≤ n → n ≤ bound → factor n ∣ n
  /-- A diagonal candidate bounds the stored factors of its multiples from p squared. -/
  multiples_le : ∀ p n, 2 ≤ p → p ^ 2 ≤ n → n ≤ bound → factor p = p → p ∣ n → factor n ≤ p

namespace SmallestPrimeFactorTableCertificate

/-- A prime in the certified interval is a diagonal entry.
The stored factor divides the prime and is at least two, so it must equal the prime.
This establishes the diagonal premise for the smallest prime factor of a composite. -/
theorem factor_eq_self_of_prime {bound : ℕ} {factor : ℕ → ℕ}
    (h : SmallestPrimeFactorTableCertificate bound factor) {p : ℕ} (hp : p.Prime) (hb : p ≤ bound) :
    factor p = p := by
  exact (Nat.dvd_prime_two_le hp (h.two_le_factor p hp.two_le hb)).mp (h.factor_dvd p hp.two_le hb)

/-- Every certified entry equals the smallest prime factor of its index.
The divisibility conditions give the lower bound. At a composite index, its smallest
prime factor is a diagonal entry and its square is at most the index, so the multiples
condition gives the reverse bound. Prime indices are diagonal directly.
This proves table correctness without a separate primality check for each candidate. -/
theorem factor_eq_minFac {bound : ℕ} {factor : ℕ → ℕ}
    (h : SmallestPrimeFactorTableCertificate bound factor) {n : ℕ} (hn : 2 ≤ n) (hb : n ≤ bound) :
    factor n = n.minFac := by
  have hn0 : 0 < n := Nat.zero_lt_two.trans_le hn
  have hlo := Nat.minFac_le_of_dvd (h.two_le_factor n hn hb) (h.factor_dvd n hn hb)
  by_cases hp : n.Prime
  · exact (h.factor_eq_self_of_prime hp hb).trans hp.minFac_eq.symm
  · have hprime := Nat.minFac_prime (Nat.ne_of_gt (Nat.one_lt_two.trans_le hn))
    have hsmall := (Nat.minFac_le hn0).trans hb
    have hdiagonal := h.factor_eq_self_of_prime hprime hsmall
    exact
      Nat.le_antisymm
        (h.multiples_le n.minFac n hprime.two_le (Nat.minFac_sq_le_self hn0 hp) hb hdiagonal
          (Nat.minFac_dvd n))
        hlo

/-- An integer from two through the certified bound is prime exactly when its
stored factor equals itself. Rewrite the table entry as Nat.minFac and apply the
prime characterization. This gives the shared membership theorem for finite witnesses. -/
theorem prime_iff_factor_eq_self {bound : ℕ} {factor : ℕ → ℕ}
    (h : SmallestPrimeFactorTableCertificate bound factor) {n : ℕ} (hn : 2 ≤ n) (hb : n ≤ bound) :
    n.Prime ↔ factor n = n := by
  rw [h.factor_eq_minFac hn hb, Nat.prime_def_minFac, and_iff_right hn]

end SmallestPrimeFactorTableCertificate

end PseudoPrime.NumberTheory
