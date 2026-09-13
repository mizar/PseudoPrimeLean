/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.ProbablePrime
import PseudoPrime.PrimeTest.MillerRabin.Defs

/-!
# Strong Lucas probable-prime test

The initial implementation follows the Selfridge branch with the Lucas index
selected by the discriminant Jacobi value.  The index is split into its odd
part and its power-of-two part, and the finite strong condition checks the
corresponding `U` and `V` values in `ZMod n`.
The explicit-parameter executable is a raw probable-prime comparison; its
totalized Jacobi branches are not a substitute for the common precheck.
-/

namespace PseudoPrime.PrimeTest

/-- The odd exponent and two-adic exponent used by the Strong Lucas test. -/
def strongLucasOddPart (n : ℕ) (D : ℤ) : ℕ :=
  oddPart (lucasProbablePrimeIndex n D)

/-- The power-of-two exponent used by the Strong Lucas test. -/
def strongLucasTwoAdicExponent (n : ℕ) (D : ℤ) : ℕ :=
  twoAdicExponent (lucasProbablePrimeIndex n D)

/-- The finite Strong Lucas probable-prime condition for proof-carrying parameters. -/
def IsStrongLucasProbablePrime (n : ℕ) (param : LucasParams) : Prop :=
  let d := strongLucasOddPart n param.D
  let s := strongLucasTwoAdicExponent n param.D
  lucasUZMod n param.P param.Q d = 0 ∨
    ∃ r ∈ List.range s, lucasVZMod n param.P param.Q (d * 2 ^ r) = 0

/-- The executable Strong Lucas test for explicit integer parameters. -/
def strongLucasWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  let d := strongLucasOddPart n D
  let s := strongLucasTwoAdicExponent n D
  (lucasUZModFast n P Q d == 0) ||
    (List.range s).any (fun r ↦ lucasVZModFast n P Q (d * 2 ^ r) == 0)

end PseudoPrime.PrimeTest
