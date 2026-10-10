/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Factorization.PrimeLeafPolicy
public import PseudoPrime.PrimeTest.Result

/-!
# PrimeTest policies for factorization leaves
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Exact factorization-leaf policy accepting precisely the natural primes.
Its acceptance predicate is `Nat.Prime`, the decision procedure is the existing exact instance,
and the soundness field is the supplied primality proof itself. There is no input-size limit
or probabilistic acceptance. BLS factor generators can use this policy independently of rho fuel.
-/
abbrev exactPrimeLeafPolicy : NumberTheory.Factorization.PrimeLeafPolicy where
  accepts := Nat.Prime
  decideAccepts := inferInstance
  sound _ h := h

/--
Build a sound factorization-leaf policy from a classifier returning `Decision n`.
Accept `n` exactly when `(classify n).toOption = some true`. Splitting the decision constructors
extracts the carried prime proof and rules out `unknown` or `notPrime` as accepted leaves.
Thus inconclusive and negative results remain available for splitting; this policy never
promotes probable-prime acceptance without a proof into a prime factorization leaf.
-/
def primeLeafPolicyOfDecision (classify : (n : ℕ) → Decision n) :
    NumberTheory.Factorization.PrimeLeafPolicy
    where
  accepts n := (classify n).toOption = some true
  decideAccepts := inferInstance
  sound n h := by
    cases hd : classify n with
    | unknown => simp only [hd, Decision.toOption, reduceCtorEq] at h
    | prime hp => exact hp
    | notPrime _ => simp only [hd, Decision.toOption, Option.some.injEq, Bool.false_eq_true] at h

end PseudoPrime.PrimeTest
