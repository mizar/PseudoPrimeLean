/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GroupGrid

/-! # Checked low-weight grouped count -/

@[expose] public section

-- The finite chain has 95 short rows.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sampled base row for budget 95. -/
def target028TwoLow569Part1Base : Array ℕ :=
  #[12, 7133]

/-- The final low-group count row for budget 95. -/
def target028TwoLow569Part1Row : Array ℕ :=
  #[12, 8273]

/-- Intermediate rows for budget 95. -/
def target028TwoLow569Part1Rows : List (Array ℕ) :=
  [#[12, 8261], #[12, 8249], #[12, 8237], #[12, 8225], #[12, 8213], #[12, 8201], #[12, 8189],
    #[12, 8177], #[12, 8165], #[12, 8153], #[12, 8141], #[12, 8129], #[12, 8117], #[12, 8105],
    #[12, 8093], #[12, 8081], #[12, 8069], #[12, 8057], #[12, 8045], #[12, 8033], #[12, 8021],
    #[12, 8009], #[12, 7997], #[12, 7985], #[12, 7973], #[12, 7961], #[12, 7949], #[12, 7937],
    #[12, 7925], #[12, 7913], #[12, 7901], #[12, 7889], #[12, 7877], #[12, 7865], #[12, 7853],
    #[12, 7841], #[12, 7829], #[12, 7817], #[12, 7805], #[12, 7793], #[12, 7781], #[12, 7769],
    #[12, 7757], #[12, 7745], #[12, 7733], #[12, 7721], #[12, 7709], #[12, 7697], #[12, 7685],
    #[12, 7673], #[12, 7661], #[12, 7649], #[12, 7637], #[12, 7625], #[12, 7613], #[12, 7601],
    #[12, 7589], #[12, 7577], #[12, 7565], #[12, 7553], #[12, 7541], #[12, 7529], #[12, 7517],
    #[12, 7505], #[12, 7493], #[12, 7481], #[12, 7469], #[12, 7457], #[12, 7445], #[12, 7433],
    #[12, 7421], #[12, 7409], #[12, 7397], #[12, 7385], #[12, 7373], #[12, 7361], #[12, 7349],
    #[12, 7337], #[12, 7325], #[12, 7313], #[12, 7301], #[12, 7289], #[12, 7277], #[12, 7265],
    #[12, 7253], #[12, 7241], #[12, 7229], #[12, 7217], #[12, 7205], #[12, 7193], #[12, 7181],
    #[12, 7169], #[12, 7157], #[12, 7145], #[12, 7133]]

set_option maxHeartbeats 0 in
-- The finite chain checks 95 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow569Part1_checked :
    weightedGroupBaseCheck 70 25 500 1 target030Seed373Row14 target028TwoLow569Part1Base = true ∧
      weightedGroupRowsCheck 1 target028TwoLow569Part1Base target028TwoLow569Part1Row
          target028TwoLow569Part1Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 95 low-group labels. -/
theorem target028TwoLow569Part1_count :
    8273 ≤ weightedPrimeCount id (List.replicate 95 70 ++ target030Seed373Weights) 95 := by
  have h :=
    target028_group_grid_general 70 25 1 95 (by decide) (by decide) target028TwoLow569Part1Base
      target028TwoLow569Part1Row target028TwoLow569Part1Rows (by decide)
      target028TwoLow569Part1_checked.1 target028TwoLow569Part1_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
