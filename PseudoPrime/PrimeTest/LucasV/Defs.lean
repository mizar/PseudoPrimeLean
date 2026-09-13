/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.Params
import PseudoPrime.PrimeTest.Lucas.Spec
import PseudoPrime.PrimeTest.Lucas.Fast
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Lucas-V probable-prime test

The initial interface follows the Selfridge branch `(D / n) = -1`.  In this
branch the Lucas-V condition is `V_(n+1) = 2 Q` in `ZMod n`.  The general
Jacobi-value form is reserved for a later extension.
-/

namespace PseudoPrime.PrimeTest

/-- The mathematical Lucas-V condition in the initial Selfridge branch. -/
def IsLucasVProbablePrime (n : ℕ) (param : LucasParams) : Prop :=
  jacobiSym param.D n = -1 ∧ lucasVZMod n param.P param.Q (n + 1) = 2 * (param.Q : ZMod n)

/-- The executable Lucas-V test for explicit integer parameters. -/
def lucasVWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  decide (jacobiSym D n = -1 ∧ lucasVZModFast n P Q (n + 1) = 2 * (Q : ZMod n))

end PseudoPrime.PrimeTest
