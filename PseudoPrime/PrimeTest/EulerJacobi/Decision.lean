/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Decision
public import PseudoPrime.PrimeTest.EulerJacobi.Prime

/-! # Certified one-sided EulerJacobi decisions -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Certified one-sided raw Euler–Jacobi comparison for natural `n` and signed integer base `a`.
Use `eulerJacobiWithIntBase_of_prime` with `decideByPrimePass`: rejection yields `notPrime`,
whereas acceptance yields `unknown`. The prime-pass theorem includes zero and non-coprime
bases, so no coprimality guard is added. This is not a full small-input primality-test contract.
-/
def EulerJacobi.decideWithIntBase (n : ℕ) (a : ℤ) : Decision n :=
  decideByPrimePass n (eulerJacobiWithIntBase n a) (fun hp ↦ eulerJacobiWithIntBase_of_prime hp a)

/--
Certified one-sided raw Euler–Jacobi comparison for natural input `n` and natural base `a`.
Prime completeness for the `n / 2` exponent supplies the implication required by
`decideByPrimePass`, including zero and non-coprime bases. Return `notPrime` only on a false
comparison and `unknown` on acceptance. Unlike a full prechecked test, this adapter does not
claim rejection of all conventional invalid or even boundary inputs.
-/
def EulerJacobi.decideWithBase (n a : ℕ) : Decision n :=
  decideByPrimePass n (eulerJacobiWithBase n a) (fun hp ↦ eulerJacobiWithBase_of_prime_of_ne_two hp)

end PseudoPrime.PrimeTest
