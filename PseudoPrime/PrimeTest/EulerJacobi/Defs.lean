/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Executable Euler–Jacobi test

The executable comparison is formulated directly in `ZMod n`, so no
natural-number encoding of the Jacobi value is needed.  This is a raw
comparison: it performs no coprimality check or common primality precheck and
is therefore not itself a complete top-level primality-test interface.
-/

namespace PseudoPrime.PrimeTest

/--
Euler–Jacobi probable-prime test for a natural-number base.

The test compares the power of the base with the Jacobi symbol in `ZMod n`.
-/
def eulerJacobiWithBase (n a : ℕ) : Bool :=
  decide ((a : ZMod n) ^ (n / 2) = (jacobiSym (a : ℤ) n : ZMod n))

/-!
The integer-base interface also compares directly in `ZMod n`, allowing
negative bases such as Lucas parameters `Q`.
-/

/-- Euler–Jacobi probable-prime test with an explicitly signed integer base. -/
def eulerJacobiWithIntBase (n : ℕ) (a : ℤ) : Bool :=
  decide ((a : ZMod n) ^ (n / 2) = (jacobiSym a n : ZMod n))

end PseudoPrime.PrimeTest
