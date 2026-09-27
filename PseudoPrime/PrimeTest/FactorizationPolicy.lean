/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Factorization.PrimeLeafPolicy
import PseudoPrime.PrimeTest.Result

/-!
# PrimeTest policies for factorization leaves
-/

namespace PseudoPrime.PrimeTest
/-- Preserve the existing exact trial-division leaf policy for BLS generators.
This policy has no input-size bound; its cost is separate from rho fuel. -/
abbrev exactPrimeLeafPolicy : NumberTheory.Factorization.PrimeLeafPolicy where
  accepts := Nat.Prime
  decideAccepts := inferInstance
  sound _ h := h

/-- Use only proved-prime decisions as factorization leaves.
Both unknown and proved-nonprime decisions leave a value available for splitting. -/
def primeLeafPolicyOfDecision (classify : (n : ℕ) → Decision n) :
    NumberTheory.Factorization.PrimeLeafPolicy where
  accepts n := (classify n).toOption = some true
  decideAccepts := inferInstance
  sound n h := by
    cases hd : classify n with
    | unknown => simp only [hd, Decision.toOption, reduceCtorEq] at h
    | prime hp => exact hp
    | notPrime _ => simp only [hd, Decision.toOption, Option.some.injEq, Bool.false_eq_true] at h

end PseudoPrime.PrimeTest
