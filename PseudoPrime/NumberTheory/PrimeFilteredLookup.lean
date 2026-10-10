/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeLookup

/-!
# Small-prime filters for certified prime lookup

Reject multiples of the first six primes before traversing a certified prime tree.
Small inputs bypass the filter, so the primes used by the filter remain searchable.
Soundness follows from the underlying certified lookup.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Test a natural against a prime tree after inexpensive divisibility filters.
Inputs at most thirteen use the tree directly. Larger inputs divisible by two, three,
five, seven, eleven, or thirteen are rejected before the tree is searched.
A positive result remains a certificate of primality for a checked tree.
Finite residue searches use this test to reduce repeated tree traversal. -/
def filteredPrimeTreeLookup (t : BinaryTree ℕ) (n : ℕ) : Bool :=
  if n - 13 == 0 then primeTreeLookup t n
  else
    (!(n % 2 == 0) && !(n % 3 == 0) && !(n % 5 == 0) && !(n % 7 == 0) && !(n % 11 == 0) &&
        !(n % 13 == 0)) &&
      primeTreeLookup t n

/-- A successful filtered lookup in a checked tree proves primality.
In either branch, extract the positive underlying tree lookup and use its soundness.
No ordering or completeness assumption is needed for this implication. -/
theorem filteredPrimeTreeLookup_prime {t : BinaryTree ℕ} (ht : primeTreeChecked t) {n : ℕ}
    (h : filteredPrimeTreeLookup t n = true) : n.Prime := by
  unfold filteredPrimeTreeLookup at h
  split at h
  next _ => exact primeTreeLookup_prime ht h
  next
    _ =>
    have hp : primeTreeLookup t n = true :=
      (show _ ∧ primeTreeLookup t n = true from by simpa only [Bool.and_eq_true] using h).2
    exact primeTreeLookup_prime ht hp

end PseudoPrime.NumberTheory
