/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Nat.Prime.Basic

/-!
# Common interface for primality tests

This file records the common executable interface and the basic correctness
properties required of a top-level primality test.
-/

namespace PseudoPrime.PrimeTest

/-- An executable primality test represented by a Boolean-valued function. -/
abbrev PrimalityTest :=
  ℕ → Bool

/--
The common specification for a top-level primality test.

The specification requires the conventional answers for `0`, `1`, `2`, and
all even inputs other than `2`, and requires every prime input to be accepted.
-/
structure PrimalityTestSpec (test : PrimalityTest) : Prop where
  zero_false : test 0 = false
  one_false : test 1 = false
  two_true : test 2 = true
  even_false : ∀ {n : ℕ}, n ≠ 2 → Even n → test n = false
  prime_true : ∀ {n : ℕ}, n.Prime → test n = true

end PseudoPrime.PrimeTest
