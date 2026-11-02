/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.UnitGenerationProductCheck

/-! # Computational boundary of the finite LLS Part 1 certificate

This module supplies the prime cap and per-position predicate used by finite Part 1 certificate
blocks for moduli from 5 through 2999, including padding beyond the last target modulus.

Keep imports and declarations limited to this computation. Adding or changing unrelated
dependencies or declarations here can invalidate the dependent finite proofs and repeat their
expensive kernel checks. Put catalog extraction, soundness, and analytic cap comparisons in
separate modules that depend on this entry, rather than importing them here.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Select the finite prime cap for a natural modulus.
Definition: 19 below 705 and 43 otherwise. Output: a natural upper bound on labels.
Role: share the exact original cap choices without depending on analytic comparisons. -/
def part1PrimeCap (q : ℕ) : ℕ :=
  if q < 705 then 19 else 43

/-- Check one position in a finite block, allowing padding beyond the target range.
Input: a block start, product and divisor code arrays, and a local index, all untrusted.
Output: the product-and-divisor coverage check below 3000, and true otherwise.
Role: retain the original modulus-to-code correspondence and final-block padding. -/
def part1ProductLeaf (start : ℕ) (codes divisorCodes : Array ℕ) (i : ℕ) : Bool :=
  if start + i < 3000 then
    unitGenerationCoverCheck (start + i) (part1PrimeCap (start + i)) ((start + i).log2 + 1)
      codes[i]! divisorCodes[i]!
  else true

end PseudoPrime.LLS
