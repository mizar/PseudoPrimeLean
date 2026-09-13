/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.BPSW.Defs
import PseudoPrime.PrimeTest.MillerRabin.Prime
import PseudoPrime.PrimeTest.StrongLucas.Prime

/-!
# Prime completeness for parameterized Baillie–PSW
-/

namespace PseudoPrime.PrimeTest

/-- A prime modulus passes the parameterized Baillie–PSW composition. -/
theorem bailliePSWWithParams_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q)
    (hjacobi : jacobiSym D n = -1) : bailliePSWWithParams n D P Q = true := by
  rw [bailliePSWWithParams, Bool.and_eq_true]
  constructor
  · exact strongMillerRabinBase2WithPrecheck_of_prime hn
  · exact strongLucasWithParams_of_prime hn D P Q hdisc hjacobi

end PseudoPrime.PrimeTest
