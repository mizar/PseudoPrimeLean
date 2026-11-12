/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.List.Basic

/-! # Sequential weighted-row checking -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Scan corresponding old, new and delayed entries for the additive row update. -/
def weightedPrimeScanRow : List ℕ → List ℕ → List ℕ → Bool
  | [], [], _ => true
  | a :: old, b :: next, c :: delayed => decide (b = a + c) && weightedPrimeScanRow old next delayed
  | _, _, _ => false

/-- Check row sizes, a positive weight and every update by a sequential list scan. -/
def weightedPrimeRowScanCheck (p N : ℕ) (old new : Array ℕ) : Bool :=
  decide (0 < p ∧ old.size = N + 1 ∧ new.size = N + 1) &&
    weightedPrimeScanRow old.toList new.toList (List.replicate p 0 ++ new.toList)

end PseudoPrime.PrimeTestBounds.MillerRabin
