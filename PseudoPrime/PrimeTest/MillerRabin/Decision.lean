/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Decision
public import PseudoPrime.PrimeTest.MillerRabin.Prime

/-! # Certified one-sided MillerRabin decisions -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Certified one-sided Strong Miller–Rabin comparison with natural base `a` at `n`.
First require `Nat.Coprime a n`; otherwise return `unknown`, since a base divisible by a
prime input would not justify rejection. With that guard, prime completeness attaches a
non-primality proof to a false comparison; a true comparison remains `unknown`.
This general-base adapter is separate from the prechecked base-two boundary contract.
-/
def MillerRabin.decideWithBase (n a : ℕ) : Decision n :=
  if h : Nat.Coprime a n then
    decideByPrimePass n (strongMillerRabinWithBase n a)
      (fun hp ↦ strongMillerRabinWithBase_of_prime hp h)
  else .unknown

/--
Apply the base-two Strong Miller–Rabin filter and its full prechecked specification at `n`.
`decideByTest` returns a non-primality proof for rejection and `unknown` for acceptance,
including the accepted input `2`. The implementation uses the proved global contract rather
than a caller-supplied coprimality hypothesis. Exact acceptance belongs to the small-input stage.
-/
def MillerRabin.decideBase2 (n : ℕ) : Decision n :=
  decideByTest strongMillerRabinBase2WithPrecheck strongMillerRabinBase2WithPrecheck_spec n

end PseudoPrime.PrimeTest
