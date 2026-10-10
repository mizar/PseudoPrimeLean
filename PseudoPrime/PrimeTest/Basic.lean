/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Common interface for primality tests

This file records the common executable interface and the basic correctness
properties required of a top-level primality test.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
A natural-number predicate executable as a Boolean primality filter.
The input is a natural number and the output records acceptance or rejection.
No correctness property is built into this abbreviation: use `PrimalityTestSpec`
to justify prime acceptance and certified rejection in the decision adapters.
-/
abbrev PrimalityTest :=
  ℕ → Bool

/--
Correctness contract for a Boolean primality filter `test`.
The fields reject `0` and `1`, accept `2`, reject all other even inputs, and accept every prime.
This is a one-sided contract: an accepted composite is permitted, so the structure does not
certify that every accepted input is prime. Decision adapters use `prime_true` contrapositively;
small-input and parity fields specify the boundary behavior of executable top-level tests.
-/
structure PrimalityTestSpec (test : PrimalityTest) : Prop where
  /-- The filter rejects zero, which is not prime. -/
  zero_false : test 0 = false
  /-- The filter rejects one, which is not prime. -/
  one_false : test 1 = false
  /-- The filter accepts the only even prime. -/
  two_true : test 2 = true
  /-- Parity alone rejects every even input other than two. -/
  even_false : ∀ {n : ℕ}, n ≠ 2 → Even n → test n = false
  /-- Every prime input is accepted; this justifies rejection by contraposition. -/
  prime_true : ∀ {n : ℕ}, n.Prime → test n = true

end PseudoPrime.PrimeTest
