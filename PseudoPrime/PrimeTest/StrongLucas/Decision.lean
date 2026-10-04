/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.StrongLucas.Prime
import PseudoPrime.PrimeTest.StrongLucas.Fast

/-! # Certified one-sided StrongLucas decisions -/

namespace PseudoPrime.PrimeTest

/-- Check the discriminant identity and Jacobi -1 branch before using prime completeness.
Invalid parameters and unsupported branches yield unknown, as does probable-prime acceptance.
Only a failed comparison with checked hypotheses proves non-primality. -/
def StrongLucas.decideWithParams (n : ℕ) (D P Q : ℤ) : Decision n :=
  if hd : D = P * P - 4 * Q then
    if hj : jacobiSym D n = -1 then
      decideByPrimePass n (strongLucasWithParamsFast n D P Q)
        (fun hp ↦ strongLucasWithParamsFast_of_prime hp D P Q hd hj)
    else .unknown
  else .unknown

end PseudoPrime.PrimeTest
