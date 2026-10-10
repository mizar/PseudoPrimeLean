/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Executable Euler–Jacobi test

The executable comparison is formulated directly in `ZMod n`, so no
natural-number encoding of the Jacobi value is needed.  This is a raw
comparison: it performs no coprimality check or common primality precheck and
is therefore not itself a complete top-level primality-test interface.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Raw Boolean Euler–Jacobi comparison for natural input `n` and natural base `a`.
Decide `(a : ZMod n) ^ (n / 2) = (jacobiSym (a : ℤ) n : ZMod n)` directly in the residue ring.
There is no coprimality guard, parity guard, or small-input precheck. The exponent is natural
integer division `n / 2`; for odd `n` it equals `(n - 1) / 2`. Prime-pass adapters use this raw
comparison without claiming that its accepted inputs are necessarily prime.
-/
def eulerJacobiWithBase (n a : ℕ) : Bool :=
  decide ((a : ZMod n) ^ (n / 2) = (jacobiSym (a : ℤ) n : ZMod n))

/-!
The integer-base interface also compares directly in `ZMod n`, allowing
negative bases such as Lucas parameters `Q`.
-/

/--
Raw Euler–Jacobi comparison with signed integer base `a` and natural modulus `n`.
The Boolean decides the equality of `a^(n / 2)` and the cast of `jacobiSym a n` in `ZMod n`.
Casting handles negative bases directly; no natural residue encoding or coprimality precheck
is performed. Strengthened Lucas composition uses this interface with its signed parameter `Q`.
-/
def eulerJacobiWithIntBase (n : ℕ) (a : ℤ) : Bool :=
  decide ((a : ZMod n) ^ (n / 2) = (jacobiSym a n : ZMod n))

end PseudoPrime.PrimeTest
