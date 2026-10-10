/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Totient

/-!
# Totient computation from prime factors

Euler's product gives the same totient as counting coprime residues.
This computational definition avoids enumerating all residues in kernel checks.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Compute Euler's totient from the distinct prime factors:
divide the modulus by their product and multiply by the product of their predecessors.
The formula also returns zero at modulus zero. This definition avoids enumerating
all coprime residues in finite kernel certificates. -/
def totientFromPrimeFactors (q : ℕ) : ℕ :=
  (q / ∏ p ∈ q.primeFactors, p) * ∏ p ∈ q.primeFactors, (p - 1)

/-- The prime-factor computation agrees with Euler's totient for every natural modulus.
Use the exact product formula, including its zero-modulus case. This equality lets
computational certificates retain the mathematical totient in their conclusions. -/
theorem totientFromPrimeFactors_eq_totient (q : ℕ) : totientFromPrimeFactors q = q.totient := by
  exact (Nat.totient_eq_div_primeFactors_mul q).symm

/-- Check that the supplied prime-factor list has product `q` and consists of primes.
Repeated entries retain their multiplicities. A successful check certifies a full
factorization without searching for the factors again. -/
def primeFactorListCheck (q : ℕ) (factors : List ℕ) : Bool :=
  decide (factors.prod = q ∧ ∀ p ∈ factors, Nat.Prime p)

/-- A successful factor-list check identifies the distinct prime factors of `q`
with the finite set of supplied entries. Use uniqueness of prime factorization
and invariance of the associated finite set under permutation. This supports
computing both the totient and the distinct-prime count from the supplied list. -/
theorem primeFactorListCheck_sound {q : ℕ} {factors : List ℕ}
    (h : primeFactorListCheck q factors = true) : q.primeFactors = factors.toFinset := by
  have hc : factors.prod = q ∧ ∀ p ∈ factors, Nat.Prime p := of_decide_eq_true h
  exact (List.toFinset_eq_of_perm _ _ (Nat.primeFactorsList_unique hc.1 hc.2)).symm

/-- Compute the Euler product from the distinct entries of a supplied factor list.
Divide `q` by their product and multiply by their predecessors. The value agrees
with the totient when the list passes the factorization check; repeated factors
contribute only once to the Euler product. -/
def totientFromFactorList (q : ℕ) (factors : List ℕ) : ℕ :=
  (q / ∏ p ∈ factors.toFinset, p) * ∏ p ∈ factors.toFinset, (p - 1)

/-- A checked factor list gives the true totient through its Euler product.
Identify its finite set with the prime factors and apply the exact totient formula.
This reflects the short arithmetic calculation used by numerical certificates. -/
theorem totientFromFactorList_eq_totient {q : ℕ} {factors : List ℕ}
    (h : primeFactorListCheck q factors = true) : totientFromFactorList q factors = q.totient := by
  rw [Nat.totient_eq_div_primeFactors_mul q, primeFactorListCheck_sound h]
  rfl

/-- Check a full prime factorization together with proposed totient `t` and
number `w` of distinct prime factors. All tests use the supplied finite list.
This Boolean result packages the arithmetic data for analytic certificates. -/
def factorListArithmeticCheck (q t w : ℕ) (factors : List ℕ) : Bool :=
  decide
    (primeFactorListCheck q factors = true ∧
      totientFromFactorList q factors = t ∧ factors.toFinset.card = w)

/-- A successful arithmetic check proves the supplied totient and distinct-prime
count. Combine the reflected Euler product with the equality of prime-factor sets.
These identities allow an analytic certificate to use computed arithmetic data. -/
theorem factorListArithmeticCheck_sound {q t w : ℕ} {factors : List ℕ}
    (h : factorListArithmeticCheck q t w factors = true) :
    q.totient = t ∧ q.primeFactors.card = w := by
  have hc :
    primeFactorListCheck q factors = true ∧
      totientFromFactorList q factors = t ∧ factors.toFinset.card = w :=
    of_decide_eq_true h
  exact
    ⟨(totientFromFactorList_eq_totient hc.1).symm.trans hc.2.1,
      congrArg Finset.card (primeFactorListCheck_sound hc.1) |>.trans hc.2.2⟩

/-- Check the product, proposed totient and distinct-prime count of a supplied
factor list. Primality is proved separately, so this test evaluates only short
integer and finite-set calculations and avoids recursive primality decisions. -/
def factorListValueCheck (q t w : ℕ) (factors : List ℕ) : Bool :=
  decide (factors.prod = q ∧ totientFromFactorList q factors = t ∧ factors.toFinset.card = w)

/-- A prime factor list whose numerical value check succeeds passes the full
arithmetic check. Reflect the product and computed values, then insert the supplied
primality proof. This permits short primality certificates rather than evaluating
primality decisions inside a large combined kernel calculation. -/
theorem factorListArithmeticCheck_of_values {q t w : ℕ} {factors : List ℕ}
    (hp : ∀ p ∈ factors, Nat.Prime p) (h : factorListValueCheck q t w factors = true) :
    factorListArithmeticCheck q t w factors = true := by
  have hc : factors.prod = q ∧ totientFromFactorList q factors = t ∧ factors.toFinset.card = w :=
    of_decide_eq_true h
  have hf : primeFactorListCheck q factors = true := decide_eq_true ⟨hc.1, hp⟩
  exact decide_eq_true ⟨hf, hc.2⟩

end PseudoPrime.NumberTheory
