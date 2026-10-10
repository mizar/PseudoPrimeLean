/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Result
public import PseudoPrime.NumberTheory.Factorization.PollardRho.Basic

/-! # Certified non-primality from a finite Pollard rho schedule -/

@[expose] public section

namespace PseudoPrime.PrimeTest.FactorWitness

/--
Search the finite Pollard-rho retry schedule `attempts` for a proper factor of `n`.
If `findFactorMany` returns a factor, its soundness theorem supplies divisibility and the strict
bounds needed by `Nat.not_prime_of_dvd_of_lt`; return that certified negative conclusion.
If the schedule finds no factor, return `unknown`, including on invalid small inputs.
The factor need not be prime; staged execution uses this adapter after probable-prime filtering.
-/
def decideMany (n : ℕ) (attempts : List NumberTheory.Factorization.PollardRho.Attempt) :
    Decision n :=
  match h : NumberTheory.Factorization.PollardRho.findFactorMany n attempts with
  | none => .unknown
  | some _ =>
    let hd := NumberTheory.Factorization.PollardRho.findFactorMany_sound h
    .notPrime (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1)

end PseudoPrime.PrimeTest.FactorWitness
