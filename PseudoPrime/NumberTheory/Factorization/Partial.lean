/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.Nat.Prime.Basic

/-!
# Partial factorization data
-/

namespace PseudoPrime.NumberTheory.Factorization

/-- A partial factor supply stores factor candidates and an unresolved cofactor.
The structure itself carries no proof: supplier soundness establishes primality and product
preservation. BLS converts these fields to prime-power certificate data. -/
structure PartialPrimeFactorSupply where
  /-- Retained factors; a supplier soundness theorem certifies their primality. -/
  factors : List ℕ
  /-- Product of leaves that remain unresolved at the supplied depth. -/
  remainder : ℕ

end PseudoPrime.NumberTheory.Factorization
