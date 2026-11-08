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

/-- The sampled base row for budget 40. -/
def target028TwoLow607Part0Base : Array ℕ :=
  #[52]

/-- The final low-group count row for budget 40. -/
def target028TwoLow607Part0Row : Array ℕ :=
  #[52]

/-- Intermediate rows for budget 40. -/
def target028TwoLow607Part0Rows : List (Array ℕ) :=
  [#[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52], #[52],
    #[52], #[52], #[52], #[52]]

set_option maxHeartbeats 0 in
-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow607Part0_checked :
    weightedGroupBaseCheck 70 40 500 0 target030Seed373Row14 target028TwoLow607Part0Base = true ∧
      weightedGroupRowsCheck 0 target028TwoLow607Part0Base target028TwoLow607Part0Row
          target028TwoLow607Part0Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow607Part0_count :
    52 ≤ weightedPrimeCount id (List.replicate 109 70 ++ target030Seed373Weights) 40 := by
  have h :=
    target028_group_grid_general 70 40 0 109 (by decide) (by decide) target028TwoLow607Part0Base
      target028TwoLow607Part0Row target028TwoLow607Part0Rows (by decide)
      target028TwoLow607Part0_checked.1 target028TwoLow607Part0_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
