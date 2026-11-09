/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Order.MinMax

/-! # Absorption in nested minima -/

@[expose] public section

namespace PseudoPrime.Order

/-- If two new candidates dominate their old counterparts, their intersection
absorbs the old counterparts from a common pointwise minimum. Compare both inequalities directly. -/
theorem min_absorb_pairs {α : Type*} [LinearOrder α] (P G S R T : α) (hG : G ≤ R) (hS : S ≤ T) :
    min (min P (min R T)) (min G S) = min P (min G S) := by
  apply le_antisymm
  · exact le_min ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _)
  · apply le_min
    · exact
        le_min (min_le_left _ _)
          (le_min ((min_le_right _ _).trans ((min_le_left _ _).trans hG))
            ((min_le_right _ _).trans ((min_le_right _ _).trans hS)))
    · exact min_le_right _ _

end PseudoPrime.Order
