/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.UnitGenerationCheckCore
public import PseudoPrime.LLS.DivisorMaskCheck
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Bitwise

/-! # Product-mask computation for finite LLS generation certificates

This module defines the executable product checker and bit masks for LLS's compact finite
certificates. The fixed five-row encoding follows that certificate representation. Finite blocks
import this computational entry without importing generation soundness or analytic bounds.

Adding or changing unrelated dependencies or declarations here can invalidate the dependent
finite proofs, even when the certificate data is unchanged. Keep this module limited to the
definitions actually evaluated by the checker; place proofs and other interfaces elsewhere.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Union the bitsets in a bounded power-of-two interval.
Input: an exclusive bound, leaf function, depth and starting index.
Output: the bitwise union over interval indices below the bound.
Role: skip an entire subtree when its first index is outside the bound. -/
def unitGenerationBoundedOr (bound : ℕ) (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, start => if start < bound then f start else 0
  | depth + 1, start =>
    if bound ≤ start then 0
    else
      unitGenerationBoundedOr bound f depth start |||
        unitGenerationBoundedOr bound f depth (start + 2 ^ depth)

/-- Evaluate a mixed-radix product in the residue ring.
Input: a modulus, generator/radix rows and a natural index, without validity assumptions.
Output: the product obtained by successive quotient and remainder digits.
Role: enumerate candidate residues for an independently checked coverage mask. -/
def unitGenerationProductValue (q : ℕ) : List (ℕ × ℕ) → ℕ → ZMod q
  | [], _ => 1
  | (p, d) :: rows, i => unitGenerationProductValue q rows (i / d) * (p : ZMod q) ^ (i % d)

/-- Decode at most five generator/radix rows from an integer certificate.
Input: an arbitrary natural code; each 18-bit word stores `64 * radix + prime`.
Output: the decoded rows with zero-radix padding removed.
Role: retain the existing exact integer data without trusting its labels or coverage. -/
def unitGenerationProductRows (code : ℕ) : List (ℕ × ℕ) :=
  ((List.range 5).map
        (fun j ↦
          let word := code / 262144 ^ j % 262144
          (word % 64, word / 64))).filter
    (fun pd ↦ pd.2 != 0)

/-- The number of mixed-radix digit combinations in the supplied rows.
Input: arbitrary generator/radix pairs. Output: the product of the radices, or one if empty.
Role: bound candidate enumeration without assuming a formula for the unit-group order. -/
def unitGenerationRadixProduct (rows : List (ℕ × ℕ)) : ℕ :=
  (rows.map Prod.snd).prod

/-- Collect candidate product residues using a shortened enumeration bound.
Input: a modulus, interval depth and arbitrary decoded rows.
Output: product bits from indices below `min q (unitGenerationRadixProduct rows)`
and `2 ^ depth`. Role: reduce kernel work while the coverage checker verifies every unit residue. -/
def unitGenerationProductMask (q depth : ℕ) (rows : List (ℕ × ℕ)) : ℕ :=
  unitGenerationBoundedOr (min q (unitGenerationRadixProduct rows))
    (fun i ↦ 2 ^ (unitGenerationProductValue q rows i).val) depth 0

/-- Decode submitted divisors and doubling levels from five packed words.
Input: an arbitrary natural code, with each 17-bit word storing `4096 * level + divisor`.
Output: the pairs whose divisor field is nonzero; the validity checker remains mandatory.
Role: represent the LLS nonunit-coverage data without trusting its factorization. -/
def unitGenerationDivisorRows (code : ℕ) : List (ℕ × ℕ) :=
  ((List.range 5).map
        (fun j ↦
          let word := code / 131072 ^ j % 131072
          (word % 4096, word / 4096))).filter
    (fun entry ↦ entry.1 != 0)

/-- Check product generation by covering residues with products and checked divisor masks.
Input: a modulus, prime cap, depth, product code and divisor code, all untrusted.
Output: true when labels pass, every submitted divisor is valid, and the two masks cover
every residue below the modulus. No completeness or minimal-level assumption is trusted.
Role: replace repeated gcd enumeration in LLS's kernel-checked finite certificates. -/
def unitGenerationCoverCheck (q cap depth code divisorCode : ℕ) : Bool :=
  let rows := unitGenerationProductRows code
  let ds := unitGenerationDivisorRows divisorCode
  rows.all
      (fun pd ↦ unitGenerationPrimes.contains pd.1 && decide (¬pd.1 ∣ q) && decide (pd.1 ≤ cap)) &&
    (divisorLevelsValid q ds &&
      decide
        (((unitGenerationProductMask q depth rows ||| divisorLevelMask ds) &&& divisorFullMask q) =
          divisorFullMask q))

end PseudoPrime.LLS
