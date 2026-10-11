/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Nat.PadicValNat

/-!
# The Kronecker symbol on all integer inputs

This mathematical specification uses the Jacobi symbol only at a positive odd denominator.
It is independent of the simultaneous symbol-and-gcd execution procedure.
The zero and negative denominator conventions differ from mathlib's natural Jacobi symbol.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The Kronecker factor at two for an integer numerator.
Even numerators give zero; residues one and seven modulo eight give one;
residues three and five give minus one. This supplies the denominator's two-power factor. -/
def kroneckerAtTwo (a : ℤ) : ℤ :=
  if a % 2 = 0 then 0 else if a % 8 = 3 ∨ a % 8 = 5 then -1 else 1

/-- The negative-denominator factor: minus one precisely when both inputs are negative.
Zero numerators have factor one. The full symbol uses this factor only at nonzero denominators. -/
def kroneckerDenominatorSign (a n : ℤ) : ℤ :=
  if a < 0 ∧ n < 0 then -1 else 1

/-- The mathematical Kronecker symbol for integer numerator and denominator.
At denominator zero it is one exactly when the numerator has absolute value one.
Otherwise remove the maximal power of two from the absolute denominator, multiply its
Kronecker factor by the Jacobi symbol at the odd quotient, and restore the denominator sign.
This is the independent specification for the executable simultaneous gcd procedure. -/
def kroneckerSym (a n : ℤ) : ℤ :=
  if n = 0 then if a.natAbs = 1 then 1 else 0
  else
    kroneckerDenominatorSign a n * kroneckerAtTwo a ^ padicValNat 2 n.natAbs *
      jacobiSym a (Nat.divMaxPow n.natAbs 2)

/-- At denominator zero, the symbol is one exactly for numerator absolute value one.
This unfolds the zero-input convention used by the executable entry point. -/
theorem kroneckerSym_zero_right (a : ℤ) :
    kroneckerSym a 0 = (if a.natAbs = 1 then 1 else 0) := rfl

/-- Both inputs zero give symbol zero, rather than mathlib's zero-denominator Jacobi value.
This boundary identity follows directly from the independent specification. -/
theorem kroneckerSym_zero_zero : kroneckerSym 0 0 = 0 := rfl

end PseudoPrime.NumberTheory
