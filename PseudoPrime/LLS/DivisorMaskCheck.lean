/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Bitwise

/-! # Divisor-mask computation for finite LLS certificates

This module computes the low-bit coverage target and masks of submitted divisor multiples used
by LLS's finite certificate checker. These operations are internal to that verification method;
the fixed certificate encoding and generator checks are defined by the LLS product checker.

Keep this computational boundary small. Adding or editing unrelated dependencies or declarations
can invalidate dependent finite certificates and repeat their expensive kernel checks. Keep the
soundness arguments, analytic interfaces and aggregate imports outside this entry.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The bitset containing exactly the natural indices below the supplied bound.
Input: any natural bound. Output: the low `q` bits, including the empty mask at zero.
Role: state exact residue coverage without importing its soundness proof. -/
def divisorFullMask (q : ℕ) : ℕ :=
  (1 <<< q) - 1

/-- Spread a bitset by adjoining shifted copies at successively doubled strides.
Input: an arbitrary level, stride and initial bitset; no validity assumptions are required.
Output: the iterated shift-and-union mask.
Role: construct submitted multiples efficiently for exact coverage checks. -/
def spreadDivisorBits : ℕ → ℕ → ℕ → ℕ
  | 0, _, bits => bits
  | level + 1, step, bits => spreadDivisorBits level (2 * step) (bits ||| (bits <<< step))

/-- Union the masks associated to submitted divisor/level pairs.
Input: an arbitrary list of pairs. Output: the union, starting each divisor mask at zero's bit.
Role: mark potential nonunits; separate validity and coverage checks justify every use. -/
def divisorLevelMask : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (d, level) :: ds => spreadDivisorBits level d 1 ||| divisorLevelMask ds

/-- Check that every submitted divisor is nontrivial and divides the modulus.
Input: a natural modulus and divisor/level pairs, with no trust in their construction.
Output: true exactly when each divisor is at least two and divides `q`.
Role: exclude unit-contaminating masks without requiring primality or complete factorization. -/
def divisorLevelsValid (q : ℕ) (ds : List (ℕ × ℕ)) : Bool :=
  ds.all (fun entry ↦ Nat.ble 2 entry.1 && (q % entry.1 == 0))

end PseudoPrime.LLS
