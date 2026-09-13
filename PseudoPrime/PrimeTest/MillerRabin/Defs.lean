/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import PseudoPrime.PrimeTest.Precheck

/-!
# Strong Miller–Rabin definitions

The exponent `n - 1` is represented as `d * 2^s`, with `d` odd.  The
finite-range formulation makes the executable Boolean test total for every
natural input; input prechecking is supplied by the surrounding interface.
-/

namespace PseudoPrime.PrimeTest

/-- The exponent of `2` in the factorization of a natural number. -/
def twoAdicExponent (m : ℕ) : ℕ :=
  padicValNat 2 m

/-- The odd part obtained after removing the computed power of `2`. -/
def oddPart (m : ℕ) : ℕ :=
  Nat.divMaxPow m 2

/-- Binary exponentiation in `ZMod`. -/
def zmodPowFast (n a : ℕ) (r : ℕ) : ZMod n :=
  npowBinRec r (a : ZMod n)

/-- The fast `ZMod` exponentiation used by the executable test. -/
def zmodPow (n a : ℕ) (r : ℕ) : ZMod n :=
  zmodPowFast n a r

/-- The proof-side definition of `ZMod` exponentiation.

This is deliberately noncomputable: all executable code goes through
`zmodPow`, while proofs can use the ordinary power notation directly. -/
noncomputable def zmodPowProof (n a : ℕ) (r : ℕ) : ZMod n :=
  (a : ZMod n) ^ r

/-- The proof-side exponentiation is definitionally ordinary `ZMod` power. -/
theorem zmodPowProof_eq_pow (n a r : ℕ) : zmodPowProof n a r = (a : ZMod n) ^ r := by rfl

/-- The executable binary exponentiation agrees with the proof-side power. -/
theorem zmodPow_eq_pow (n a r : ℕ) : zmodPow n a r = (a : ZMod n) ^ r := by
  unfold zmodPow zmodPowFast
  induction r with
  | zero => rw [npowBinRec_zero, pow_zero]
  | succ r ih => rw [npowBinRec_succ, pow_succ, ih]

/-- The executable and proof-side exponentiations are equal. -/
theorem zmodPow_eq_zmodPowProof (n a r : ℕ) : zmodPow n a r = zmodPowProof n a r := by
  rw [zmodPow_eq_pow, zmodPowProof_eq_pow]

/-- The computed two-adic part and odd part reconstruct the input. -/
theorem twoAdicPart_mul_oddPart (m : ℕ) : 2 ^ twoAdicExponent m * oddPart m = m := by
  simpa only [twoAdicExponent, oddPart, Nat.mul_comm] using Nat.divMaxPow_mul_pow_padicValNat 2 m

/- The quotient really is odd for a nonzero input. -/
theorem oddPart_odd {m : ℕ} (hm : m ≠ 0) : Odd (oddPart m) := by
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  simpa only [oddPart] using (Nat.not_dvd_divMaxPow (by decide) hm)

/-- The proof-side finite Strong Miller–Rabin condition for a base. -/
def IsStrongMillerRabinProbablePrime (n a : ℕ) : Prop :=
  let s := twoAdicExponent (n - 1)
  let d := oddPart (n - 1)
  zmodPowProof n a d = 1 ∨ ∃ r ∈ List.range s, zmodPowProof n a (d * 2 ^ r) = n - 1

/-- The executable finite Strong Miller–Rabin condition. -/
def IsStrongMillerRabinProbablePrimeFast (n a : ℕ) : Prop :=
  let s := twoAdicExponent (n - 1)
  let d := oddPart (n - 1)
  zmodPow n a d = 1 ∨ ∃ r ∈ List.range s, zmodPow n a (d * 2 ^ r) = n - 1

/-- Executable Strong Miller–Rabin test for an explicit natural base. -/
def strongMillerRabinWithBase (n a : ℕ) : Bool :=
  let s := twoAdicExponent (n - 1)
  let d := oddPart (n - 1)
  decide (zmodPow n a d = 1 ∨ ∃ r ∈ List.range s, zmodPow n a (d * 2 ^ r) = n - 1)

/-- The fast and proof-side Strong Miller–Rabin conditions are equivalent. -/
theorem isStrongMillerRabinProbablePrimeFast_iff {n a : ℕ} :
    IsStrongMillerRabinProbablePrimeFast n a ↔ IsStrongMillerRabinProbablePrime n a := by
  simp only [IsStrongMillerRabinProbablePrimeFast, IsStrongMillerRabinProbablePrime,
    zmodPow_eq_zmodPowProof]

/-- Strong Miller–Rabin with the conventional base `2`. -/
def strongMillerRabinBase2 (n : ℕ) : Bool :=
  strongMillerRabinWithBase n 2

/-- Base `2` Strong Miller–Rabin preceded by the common small-input precheck. -/
def strongMillerRabinBase2WithPrecheck (n : ℕ) : Bool :=
  match primalityPrecheck n with
  | some result => result
  | none => strongMillerRabinBase2 n

end PseudoPrime.PrimeTest
