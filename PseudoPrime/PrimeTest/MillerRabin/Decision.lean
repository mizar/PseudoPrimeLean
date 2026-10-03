/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.MillerRabin.Prime

/-! # Certified one-sided MillerRabin decisions -/

namespace PseudoPrime.PrimeTest

/-- Refute primality using Miller-Rabin only when the supplied base is coprime to n.
A non-coprime base may equal a prime input, so that case remains unknown. -/
def MillerRabin.decideWithBase (n a : ℕ) : Decision n :=
  if h : Nat.Coprime a n then
    decideByPrimePass n (strongMillerRabinWithBase n a)
      (fun hp ↦ strongMillerRabinWithBase_of_prime hp h)
  else .unknown

/-- Apply the full prechecked test specification; rejection proves non-primality.
Acceptance remains unknown, including at two; use SmallInput for an exact small decision. -/
def MillerRabin.decideBase2 (n : ℕ) : Decision n :=
  decideByTest strongMillerRabinBase2WithPrecheck strongMillerRabinBase2WithPrecheck_spec n

end PseudoPrime.PrimeTest
