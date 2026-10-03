/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.Nat.Basic

/-!
# Proper factor specification
-/

namespace PseudoPrime.NumberTheory.Factorization

/-- `d` is a nontrivial proper divisor of `n`, independently of the search algorithm. -/
def ProperFactor (n d : ℕ) : Prop :=
  1 < d ∧ d < n ∧ d ∣ n

end PseudoPrime.NumberTheory.Factorization
