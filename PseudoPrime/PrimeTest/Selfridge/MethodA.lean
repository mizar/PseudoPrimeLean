/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.StrongLucas.Spec
import PseudoPrime.PrimeTest.StrongLucas.Prime
import PseudoPrime.PrimeTest.Selfridge.Candidates
import PseudoPrime.PrimeTest.Selfridge.Params

/-!
# Selfridge Method A parameters

This module connects the standard Method A choice `P = 1` and
`Q = (1 - D) / 4` to the parameterized Strong Lucas interface.  The search
for an admissible `D` remains a separate executable layer.
-/

namespace PseudoPrime.PrimeTest

/-- Strong Lucas evaluated with the standard Selfridge Method A parameters. -/
def strongLucasMethodA (n : ℕ) (D : ℤ) (_hmod : (1 - D) % 4 = 0) : Bool :=
  strongLucasWithParams n D 1 ((1 - D) / 4)

/-- Method A is the parameterized Strong Lucas test at `P = 1`. -/
theorem strongLucasMethodA_eq_parameterized (n : ℕ) (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    strongLucasMethodA n D hmod =
      strongLucasWithParams n D (LucasParams.methodA D hmod).P (LucasParams.methodA D hmod).Q := by
  rw [LucasParams.methodA_P, LucasParams.methodA_Q]
  rfl

/-- A prime modulus passes Selfridge Method A in the Jacobi `-1` branch. -/
theorem strongLucasMethodA_of_prime {n : ℕ} (hn : n.Prime) (D : ℤ) (hmod : (1 - D) % 4 = 0)
    (hjacobi : jacobiSym D n = -1) : strongLucasMethodA n D hmod = true := by
  rw [strongLucasMethodA_eq_parameterized]
  exact
    strongLucasWithParams_of_prime hn D (LucasParams.methodA D hmod).P
      (LucasParams.methodA D hmod).Q (LucasParams.methodA D hmod).discr hjacobi

end PseudoPrime.PrimeTest
