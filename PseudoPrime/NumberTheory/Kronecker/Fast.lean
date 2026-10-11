/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Normalization
public import PseudoPrime.NumberTheory.Jacobi.Symbol

/-! # Symbol-only Kronecker execution with all-input Jacobi correction

The odd symbol recursion returns only a sign. No shared gcd state, gcd restoration,
or Fibonacci fuel selection is evaluated. A zero normalization coefficient returns immediately.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Symbol-only execution at a nonzero integer denominator.
Each input supplies one maximal two-power decomposition; signs and two-power factors
normalize the odd Jacobi recursion. A zero coefficient skips that recursion.
The optional correction gives mathlib's natural-denominator Jacobi convention.
Only the symbol is returned: no gcd trajectory or common two-power is reconstructed. -/
def kroneckerSymNonzeroFast (a n : ℤ) (jacobiCorrection : Bool := false) : ℤ :=
  let (ea, da) := Nat.maxPowDvdDiv 2 a.natAbs
  let (en, dn) := Nat.maxPowDvdDiv 2 n.natAbs
  let s := kroneckerNormalizationSign a n ea en dn
  let c := if jacobiCorrection then kroneckerTwoPowerFactor a en * s else s
  if c = 0 then 0 else Jacobi.symbolNat (da % dn) dn c

/-- Returning immediately at a zero coefficient preserves its product with any symbol.
This certifies the symbol-only normalization's early exit. -/
private theorem zeroGuard_mul (c j : ℤ) : (if c = 0 then 0 else c * j) = c * j := by
  by_cases h : c = 0 <;> simp only [h, ite_true, ite_false, zero_mul]

/-- At a nonzero denominator, symbol-only execution gives the specified Kronecker value.
With correction enabled, multiply by the denominator's two-power factor.
The certified odd Jacobi recursion and two-adic normalization identify the output.
This supplies both all-integer Kronecker and all-natural-denominator Jacobi adapters. -/
theorem kroneckerSymNonzeroFast_spec (a n : ℤ) (b : Bool) (hn : n ≠ 0) :
    kroneckerSymNonzeroFast a n b =
      if b then kroneckerTwoPowerFactor a (padicValNat 2 n.natAbs) * kroneckerSym a n
      else kroneckerSym a n := by
  dsimp only [kroneckerSymNonzeroFast]
  rw [Jacobi.symbolNat_eq_reference, zeroGuard_mul]
  simp only [Nat.fst_maxPowDvdDiv, Nat.snd_maxPowDvdDiv]
  rw [Jacobi.jacobiNat_eq _ _ (TwoAdic.oddPart_odd n.natAbs (Int.natAbs_ne_zero.mpr hn)),
    Int.natCast_emod, ← jacobiSym.mod_left, kroneckerSym_two_adic a n hn]
  simp only [ite_mul, mul_assoc]

/-- Executable Kronecker symbol for every pair of integers, without computing a gcd.
At denominator zero return one exactly when the numerator's absolute value is one.
Other denominators use the symbol-only normalized recursion, including zero numerators.
This is the execution counterpart of the independent specification `kroneckerSym`. -/
def kroneckerSymFast (a n : ℤ) : ℤ :=
  if n = 0 then (if a.natAbs = 1 then 1 else 0) else kroneckerSymNonzeroFast a n

/-- Symbol-only Kronecker execution equals the specification on all integer inputs.
The zero-denominator branch uses the boundary identity; other inputs use normalization.
This transfers mathematical Kronecker statements to the executable entry. -/
theorem kroneckerSymFast_eq (a n : ℤ) : kroneckerSymFast a n = kroneckerSym a n := by
  by_cases hn : n = 0
  · subst n
    simp only [kroneckerSymFast, ite_true, kroneckerSym_zero_right]
  · rw [kroneckerSymFast, ite_eq_right hn, kroneckerSymNonzeroFast_spec a n false hn]
    rfl

end PseudoPrime.NumberTheory
