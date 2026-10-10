/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Defs
public import PseudoPrime.PrimeTest.StrongLucas.Defs

/-!
# Parameterized Baillie–PSW composition

The executable composition keeps the Selfridge parameters explicit.  Search
and parameter selection remain in the separate Selfridge layer.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Parameterized Boolean conjunction of base-two Strong Miller–Rabin and Strong Lucas.
The natural input is `n`; `D`, `P`, and `Q` are the caller-supplied integer discriminant and
Lucas parameters. Evaluate `strongMillerRabinBase2WithPrecheck n` and
`strongLucasWithParams n D P Q`; acceptance requires both. This definition does not select
Selfridge parameters. Prime completeness additionally requires the discriminant and Jacobi
hypotheses supplied by `bailliePSWWithParams_of_prime`.
-/
def bailliePSWWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  strongMillerRabinBase2WithPrecheck n && strongLucasWithParams n D P Q

end PseudoPrime.PrimeTest
