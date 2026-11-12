/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Basic

/-! # Integer execution of fixed-point logarithm walks -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Starting at positive `n` with fixed-point bounds `lo` and `hi` at scale `S`,
advance `k` integer positions by outward-rounded rational increments. The
execution carries only the current state and never accesses a list by index. -/
def logWalk (S : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | _, lo, hi, 0 => (lo, hi)
  | n, lo, hi, k + 1 => logWalk S (n + 1) (lo + 2 * S / (2 * n + 1)) (hi + (S / n + 1)) k

end PseudoPrime.Analysis
