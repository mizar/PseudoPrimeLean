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

/-- The sampled base row for budget 132. -/
def target028TwoLow618Part1Base : Array ℕ :=
  #[451, 120086]

/-- The final low-group count row for budget 132. -/
def target028TwoLow618Part1Row : Array ℕ :=
  #[451, 169245]

/-- Intermediate rows for budget 132. -/
def target028TwoLow618Part1Rows : List (Array ℕ) :=
  [#[451, 168794], #[451, 168343], #[451, 167892], #[451, 167441], #[451, 166990], #[451, 166539],
    #[451, 166088], #[451, 165637], #[451, 165186], #[451, 164735], #[451, 164284], #[451, 163833],
    #[451, 163382], #[451, 162931], #[451, 162480], #[451, 162029], #[451, 161578], #[451, 161127],
    #[451, 160676], #[451, 160225], #[451, 159774], #[451, 159323], #[451, 158872], #[451, 158421],
    #[451, 157970], #[451, 157519], #[451, 157068], #[451, 156617], #[451, 156166], #[451, 155715],
    #[451, 155264], #[451, 154813], #[451, 154362], #[451, 153911], #[451, 153460], #[451, 153009],
    #[451, 152558], #[451, 152107], #[451, 151656], #[451, 151205], #[451, 150754], #[451, 150303],
    #[451, 149852], #[451, 149401], #[451, 148950], #[451, 148499], #[451, 148048], #[451, 147597],
    #[451, 147146], #[451, 146695], #[451, 146244], #[451, 145793], #[451, 145342], #[451, 144891],
    #[451, 144440], #[451, 143989], #[451, 143538], #[451, 143087], #[451, 142636], #[451, 142185],
    #[451, 141734], #[451, 141283], #[451, 140832], #[451, 140381], #[451, 139930], #[451, 139479],
    #[451, 139028], #[451, 138577], #[451, 138126], #[451, 137675], #[451, 137224], #[451, 136773],
    #[451, 136322], #[451, 135871], #[451, 135420], #[451, 134969], #[451, 134518], #[451, 134067],
    #[451, 133616], #[451, 133165], #[451, 132714], #[451, 132263], #[451, 131812], #[451, 131361],
    #[451, 130910], #[451, 130459], #[451, 130008], #[451, 129557], #[451, 129106], #[451, 128655],
    #[451, 128204], #[451, 127753], #[451, 127302], #[451, 126851], #[451, 126400], #[451, 125949],
    #[451, 125498], #[451, 125047], #[451, 124596], #[451, 124145], #[451, 123694], #[451, 123243],
    #[451, 122792], #[451, 122341], #[451, 121890], #[451, 121439], #[451, 120988], #[451, 120537],
    #[451, 120086]]

set_option maxHeartbeats 0 in
-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow618Part1_checked :
    weightedGroupBaseCheck 70 62 500 1 target030Seed373Row14 target028TwoLow618Part1Base = true ∧
      weightedGroupRowsCheck 1 target028TwoLow618Part1Base target028TwoLow618Part1Row
          target028TwoLow618Part1Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow618Part1_count :
    169245 ≤ weightedPrimeCount id (List.replicate 109 70 ++ target030Seed373Weights) 132 := by
  have h :=
    target028_group_grid_general 70 62 1 109 (by decide) (by decide) target028TwoLow618Part1Base
      target028TwoLow618Part1Row target028TwoLow618Part1Rows (by decide)
      target028TwoLow618Part1_checked.1 target028TwoLow618Part1_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
