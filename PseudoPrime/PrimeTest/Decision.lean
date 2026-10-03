/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Basic
import PseudoPrime.PrimeTest.Result

/-! # Sound one-sided adapters for probable-prime tests -/

namespace PseudoPrime.PrimeTest

/-- Rejection by a test accepting every prime proves non-primality.
The prime_true field supplies the contrapositive; acceptance alone proves nothing. -/
theorem PrimalityTestSpec.not_prime_of_false {test : PrimalityTest} (spec : PrimalityTestSpec test)
    {n : ℕ} (h : test n = false) : ¬Nat.Prime n := by
  intro hp
  exact Bool.noConfusion (h.symm.trans (spec.prime_true hp))

/-- Convert a specified Boolean test to a certified one-sided decision.
A rejected input is notPrime; an accepted input remains unknown, even at two.
Exact small-input decisions belong to the independent trial-division entry. -/
def decideByTest (test : PrimalityTest) (spec : PrimalityTestSpec test) (n : ℕ) : Decision n :=
  if h : test n = false then .notPrime (spec.not_prime_of_false h) else .unknown

/-- Extract a negative conclusion from a comparison with a proved prime-pass implication.
This weaker interface allows raw or guarded comparisons without claiming a full test spec.
Acceptance remains unknown; any side conditions must be discharged by the caller. -/
def decideByPrimePass (n : ℕ) (accepted : Bool) (primePass : Nat.Prime n → accepted = true) :
    Decision n :=
  if h : accepted = false then .notPrime (fun hp ↦ Bool.noConfusion (h.symm.trans (primePass hp)))
  else .unknown

end PseudoPrime.PrimeTest
