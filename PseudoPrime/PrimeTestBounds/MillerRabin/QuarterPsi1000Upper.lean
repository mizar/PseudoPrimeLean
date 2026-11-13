/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsi1000Sharp

/-! # Chebyshev upper boundary at 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The existing checked prime-power rows give the unconditional upper bound
`psi 1000 ≤ 1000`. This improves the boundary term in Euler-tail estimates. -/
theorem quarter_psi1000_upper : Chebyshev.psi 1000 ≤ 1000 := by linarith only [quarter_psi1000_997]

end PseudoPrime.PrimeTestBounds.MillerRabin
