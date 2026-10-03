/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Result
import PseudoPrime.NumberTheory.Factorization.PollardRho.Basic

/-! # Certified non-primality from a finite Pollard rho schedule -/

namespace PseudoPrime.PrimeTest.FactorWitness

/-- Run the supplied retry schedule and refute primality only upon finding a proper factor.
The factor need not be prime. Empty schedules, zero fuel and exhausted searches yield unknown,
including on zero and one. The underlying factor API remains available to factor consumers. -/
def decideMany (n : ℕ) (attempts : List NumberTheory.Factorization.PollardRho.Attempt) :
    Decision n :=
  match h : NumberTheory.Factorization.PollardRho.findFactorMany n attempts with
  | none => .unknown
  | some _ =>
    let hd := NumberTheory.Factorization.PollardRho.findFactorMany_sound h
    .notPrime (Nat.not_prime_of_dvd_of_lt hd.2.2 hd.1 hd.2.1)

end PseudoPrime.PrimeTest.FactorWitness
