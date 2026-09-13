/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.MillerRabin.Defs
import PseudoPrime.PrimeTest.StrongLucas.Defs

/-!
# Parameterized Baillie–PSW composition

The executable composition keeps the Selfridge parameters explicit.  Search
and parameter selection remain in the separate Selfridge layer.
-/

namespace PseudoPrime.PrimeTest

/-- Baillie–PSW with an explicit discriminant and Lucas parameter triple. -/
def bailliePSWWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  strongMillerRabinBase2WithPrecheck n && strongLucasWithParams n D P Q

end PseudoPrime.PrimeTest
