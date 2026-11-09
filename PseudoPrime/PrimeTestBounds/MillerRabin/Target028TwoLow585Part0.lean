/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupGrid

/-! # Checked low-weight grouped count -/

@[expose] public section

-- The finite chain has 109 short rows.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sampled base row for budget 25. -/
def target028TwoLow585Part0Base : Array ℕ :=
  #[12]

/-- The final low-group count row for budget 25. -/
def target028TwoLow585Part0Row : Array ℕ :=
  #[12]

/-- Intermediate rows for budget 25. -/
def target028TwoLow585Part0Rows : List (Array ℕ) :=
  [#[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12], #[12],
    #[12], #[12], #[12], #[12]]

set_option maxHeartbeats 0 in
-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow585Part0_checked :
    weightedGroupBaseCheck 70 25 500 0 primeSeed373Row14 target028TwoLow585Part0Base = true ∧
      weightedGroupRowsCheck 0 target028TwoLow585Part0Base target028TwoLow585Part0Row
          target028TwoLow585Part0Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow585Part0_count :
    12 ≤ weightedPrimeCount id (List.replicate 109 70 ++ primeSeed373Weights) 25 := by
  have h :=
    target028_group_grid_general 70 25 0 109 (by decide) (by decide) target028TwoLow585Part0Base
      target028TwoLow585Part0Row target028TwoLow585Part0Rows (by decide)
      target028TwoLow585Part0_checked.1 target028TwoLow585Part0_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
