/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Decision
public import PseudoPrime.PrimeTest.Lucas.Prime

/-! # Certified one-sided Lucas decisions -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Certified one-sided Lucas comparison for input `n` and integer parameters `D`, `P`, `Q`.
Check `D = P * P - 4 * Q` and `jacobiSym D n = -1` before evaluating `lucasWithParams`.
If either parameter check fails, return `unknown`; otherwise prime completeness lets a false
comparison certify `notPrime`. A true comparison also remains `unknown`, because these
parameter checks and a probable-prime pass are not a proof of primality.
Individual-method filters and staged execution use this guarded decision interface.
-/
def Lucas.decideWithParams (n : ℕ) (D P Q : ℤ) : Decision n :=
  if hd : D = P * P - 4 * Q then
    if hj : jacobiSym D n = -1 then
      decideByPrimePass n (lucasWithParams n D P Q)
        (fun hp ↦ lucasWithParams_of_prime hp D P Q hd hj)
    else .unknown
  else .unknown

end PseudoPrime.PrimeTest
