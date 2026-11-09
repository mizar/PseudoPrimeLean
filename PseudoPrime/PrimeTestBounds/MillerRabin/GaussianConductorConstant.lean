/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic

/-! The conductor coefficient in the Gaussian zero-mass estimate. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The exact conductor coefficient from the Gaussian zero-mass estimate.
The refined comparison retains this value through primitive character averaging. -/
noncomputable def gaussianConductorCoeff : ℝ :=
  20115621 / 50000000

end PseudoPrime.PrimeTestBounds.MillerRabin
