/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Basic
public import PseudoPrime.PrimeTest.Result

/-! # Sound one-sided adapters for probable-prime tests -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
A filter satisfying `spec` cannot reject a prime input.
Given `test n = false`, conclude `¬Nat.Prime n` without any assumption on the size or parity
of `n`. The proof contradicts `spec.prime_true` using the distinct Boolean constructors.
This is the soundness step used by `decideByTest` to attach a proof to rejection.
-/
theorem PrimalityTestSpec.not_prime_of_false {test : PrimalityTest} (spec : PrimalityTestSpec test)
    {n : ℕ} (h : test n = false) : ¬Nat.Prime n := by
  intro hp
  exact Bool.noConfusion (h.symm.trans (spec.prime_true hp))

/--
Turn `test` and its one-sided correctness contract `spec` into a certified result at `n`.
If `test n = false`, return `notPrime` with `spec.not_prime_of_false`; otherwise return
`unknown`. Acceptance, including acceptance of `2`, does not certify primality here.
Staged execution combines this filter with separate exact small-input and certificate stages.
-/
def decideByTest (test : PrimalityTest) (spec : PrimalityTestSpec test) (n : ℕ) : Decision n :=
  if h : test n = false then .notPrime (spec.not_prime_of_false h) else .unknown

/--
Equal Boolean filters yield equal certified decisions at every input `n`.
The premises give contracts `spec₁`, `spec₂` and function equality `test₁ = test₂`.
After eliminating that equality, proof irrelevance makes the two decisions definitionally equal.
This transports an all-input Boolean refactoring to callers of the certified adapter.
-/
theorem decideByTest_congr {test₁ test₂ : PrimalityTest} (spec₁ : PrimalityTestSpec test₁)
    (spec₂ : PrimalityTestSpec test₂) (h : test₁ = test₂) (n : ℕ) :
    decideByTest test₁ spec₁ n = decideByTest test₂ spec₂ n := by
  cases h
  rfl

/--
Build a certified one-sided result from a Boolean `accepted` at the input `n`.
The supplied implication `primePass` must prove that every proof of `Nat.Prime n` forces
`accepted = true`. A false result is returned as `notPrime` by contradiction; a true result
remains `unknown`. Guarded comparison methods use this weaker interface without requiring
all small-input and parity fields of `PrimalityTestSpec`.
-/
def decideByPrimePass (n : ℕ) (accepted : Bool) (primePass : Nat.Prime n → accepted = true) :
    Decision n :=
  if h : accepted = false then .notPrime (fun hp ↦ Bool.noConfusion (h.symm.trans (primePass hp)))
  else .unknown

end PseudoPrime.PrimeTest
