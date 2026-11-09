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

/-- The sampled base row for budget 37. -/
def target028TwoLow597Part0Base : Array ℕ :=
  #[38]

/-- The final low-group count row for budget 37. -/
def target028TwoLow597Part0Row : Array ℕ :=
  #[38]

/-- Intermediate rows for budget 37. -/
def target028TwoLow597Part0Rows : List (Array ℕ) :=
  [#[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38], #[38],
    #[38], #[38], #[38], #[38]]

set_option maxHeartbeats 0 in
-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow597Part0_checked :
    weightedGroupBaseCheck 70 37 500 0 primeSeed373Row14 target028TwoLow597Part0Base = true ∧
      weightedGroupRowsCheck 0 target028TwoLow597Part0Base target028TwoLow597Part0Row
          target028TwoLow597Part0Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow597Part0_count :
    38 ≤ weightedPrimeCount id (List.replicate 109 70 ++ primeSeed373Weights) 37 := by
  have h :=
    target028_group_grid_general 70 37 0 109 (by decide) (by decide) target028TwoLow597Part0Base
      target028TwoLow597Part0Row target028TwoLow597Part0Rows (by decide)
      target028TwoLow597Part0_checked.1 target028TwoLow597Part0_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
