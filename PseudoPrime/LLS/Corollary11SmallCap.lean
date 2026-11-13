/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Basic

/-! # Natural cap for finite nonresidue witnesses -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Natural cap for the finite nonresidue witness, chosen below a certified
logarithmic-square bound in each interval. -/
def smallNonresidueCap (q : ℕ) : ℕ :=
  if q < 7 then 3 else if q < 23 then 4 else if q < 311 then 8 else 18

end PseudoPrime.LLS
