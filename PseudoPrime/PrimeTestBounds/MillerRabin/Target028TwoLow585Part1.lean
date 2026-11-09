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

/-- The sampled base row for budget 105. -/
def target028TwoLow585Part1Base : Array ℕ :=
  #[33, 15832]

/-- The final low-group count row for budget 105. -/
def target028TwoLow585Part1Row : Array ℕ :=
  #[33, 19429]

/-- Intermediate rows for budget 105. -/
def target028TwoLow585Part1Rows : List (Array ℕ) :=
  [#[33, 19396], #[33, 19363], #[33, 19330], #[33, 19297], #[33, 19264], #[33, 19231], #[33, 19198],
    #[33, 19165], #[33, 19132], #[33, 19099], #[33, 19066], #[33, 19033], #[33, 19000],
    #[33, 18967], #[33, 18934], #[33, 18901], #[33, 18868], #[33, 18835], #[33, 18802],
    #[33, 18769], #[33, 18736], #[33, 18703], #[33, 18670], #[33, 18637], #[33, 18604],
    #[33, 18571], #[33, 18538], #[33, 18505], #[33, 18472], #[33, 18439], #[33, 18406],
    #[33, 18373], #[33, 18340], #[33, 18307], #[33, 18274], #[33, 18241], #[33, 18208],
    #[33, 18175], #[33, 18142], #[33, 18109], #[33, 18076], #[33, 18043], #[33, 18010],
    #[33, 17977], #[33, 17944], #[33, 17911], #[33, 17878], #[33, 17845], #[33, 17812],
    #[33, 17779], #[33, 17746], #[33, 17713], #[33, 17680], #[33, 17647], #[33, 17614],
    #[33, 17581], #[33, 17548], #[33, 17515], #[33, 17482], #[33, 17449], #[33, 17416],
    #[33, 17383], #[33, 17350], #[33, 17317], #[33, 17284], #[33, 17251], #[33, 17218],
    #[33, 17185], #[33, 17152], #[33, 17119], #[33, 17086], #[33, 17053], #[33, 17020],
    #[33, 16987], #[33, 16954], #[33, 16921], #[33, 16888], #[33, 16855], #[33, 16822],
    #[33, 16789], #[33, 16756], #[33, 16723], #[33, 16690], #[33, 16657], #[33, 16624],
    #[33, 16591], #[33, 16558], #[33, 16525], #[33, 16492], #[33, 16459], #[33, 16426],
    #[33, 16393], #[33, 16360], #[33, 16327], #[33, 16294], #[33, 16261], #[33, 16228],
    #[33, 16195], #[33, 16162], #[33, 16129], #[33, 16096], #[33, 16063], #[33, 16030],
    #[33, 15997], #[33, 15964], #[33, 15931], #[33, 15898], #[33, 15865], #[33, 15832]]

set_option maxHeartbeats 0 in
-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow585Part1_checked :
    weightedGroupBaseCheck 70 35 500 1 primeSeed373Row14 target028TwoLow585Part1Base = true ∧
      weightedGroupRowsCheck 1 target028TwoLow585Part1Base target028TwoLow585Part1Row
          target028TwoLow585Part1Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow585Part1_count :
    19429 ≤ weightedPrimeCount id (List.replicate 109 70 ++ primeSeed373Weights) 105 := by
  have h :=
    target028_group_grid_general 70 35 1 109 (by decide) (by decide) target028TwoLow585Part1Base
      target028TwoLow585Part1Row target028TwoLow585Part1Rows (by decide)
      target028TwoLow585Part1_checked.1 target028TwoLow585Part1_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
