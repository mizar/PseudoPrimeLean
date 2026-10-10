/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Params
public import PseudoPrime.PrimeTest.Lucas.Spec
public import PseudoPrime.PrimeTest.Lucas.Fast
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Lucas-V probable-prime test

The initial interface follows the Selfridge branch `(D / n) = -1`.  In this
branch the Lucas-V condition is `V_(n+1) = 2 Q` in `ZMod n`.  The general
Jacobi-value form is reserved for a later extension.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Lucas-V condition for natural `n` and proof-carrying recurrence parameters `param`.
Require both `jacobiSym param.D n = -1` and `V_(n+1) = 2Q` in `ZMod n`.
The discriminant equation is stored in `param`; this proposition covers the minus-one branch
used by Selfridge selection, not a general Jacobi-index Lucas-V criterion.
Executable acceptance is related to this proposition by the specification theorem.
-/
def IsLucasVProbablePrime (n : ℕ) (param : LucasParams) : Prop :=
  jacobiSym param.D n = -1 ∧ lucasVZMod n param.P param.Q (n + 1) = 2 * (param.Q : ZMod n)

/--
Executable Boolean Lucas-V comparison for natural `n` and signed parameters `D`, `P`, `Q`.
Decide the conjunction of Jacobi value `-1` and the fast modular identity `V_(n+1) = 2Q`.
The definition does not check the discriminant equation or a primality precheck; guarded decision
adapters supply the required parameter checks before treating a failure as certified rejection.
-/
def lucasVWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  decide (jacobiSym D n = -1 ∧ lucasVZModFast n P Q (n + 1) = 2 * (Q : ZMod n))

end PseudoPrime.PrimeTest
