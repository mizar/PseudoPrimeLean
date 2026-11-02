/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Basic

/-! # Computational core for finite LLS generation certificates

This module supplies the fixed prime-label table and balanced Boolean traversal used by LLS's
finite unit-generation certificates. The label table reflects the chosen certificate data.

Keep this computational dependency boundary small. Adding or changing unrelated imports or
declarations here can invalidate dependent finite proofs and trigger expensive kernel rechecking.
Place soundness proofs and analytic interfaces in separate modules.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The prime labels allowed in finite generation data.
Input: none. Output: the fixed list of primes at most 81.
Role: check labels without importing generation soundness or analytic bounds. -/
def unitGenerationPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]

/-- Check a Boolean predicate on a power-of-two interval.
Input: the predicate, depth and starting index; no assumptions are required.
Output: the conjunction of its values on the next `2 ^ depth` indices.
Role: combine bounded certificate windows with balanced kernel recursion. -/
def unitGenerationAll (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, start => f start
  | depth + 1, start =>
    unitGenerationAll f depth start && unitGenerationAll f depth (start + 2 ^ depth)

end PseudoPrime.LLS
