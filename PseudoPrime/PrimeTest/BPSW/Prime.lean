/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.BPSW.Defs
public import PseudoPrime.PrimeTest.MillerRabin.Prime
public import PseudoPrime.PrimeTest.StrongLucas.Prime

/-!
# Prime completeness for parameterized Baillie–PSW
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Every prime modulus passes the parameterized ordinary BPSW conjunction.
The premises require `n.Prime`, `D = P * P - 4 * Q`, and `jacobiSym D n = -1`.
The proof splits Boolean conjunction and applies prime completeness of the prechecked
base-two Miller–Rabin test and the Strong Lucas test. Selfridge selection later supplies
these parameter hypotheses; this theorem alone does not justify arbitrary parameter triples.
-/
theorem bailliePSWWithParams_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q)
    (hjacobi : jacobiSym D n = -1) : bailliePSWWithParams n D P Q = true := by
  rw [bailliePSWWithParams, Bool.and_eq_true]
  constructor
  · exact strongMillerRabinBase2WithPrecheck_of_prime hn
  · exact strongLucasWithParams_of_prime hn D P Q hdisc hjacobi

end PseudoPrime.PrimeTest
