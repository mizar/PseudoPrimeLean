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

/-- The sampled base row for budget 117. -/
def target028TwoLow597Part1Base : Array ℕ :=
  #[106, 39839]

/-- The final low-group count row for budget 117. -/
def target028TwoLow597Part1Row : Array ℕ :=
  #[106, 51393]

/-- Intermediate rows for budget 117. -/
def target028TwoLow597Part1Rows : List (Array ℕ) :=
  [#[106, 51287], #[106, 51181], #[106, 51075], #[106, 50969], #[106, 50863], #[106, 50757],
    #[106, 50651], #[106, 50545], #[106, 50439], #[106, 50333], #[106, 50227], #[106, 50121],
    #[106, 50015], #[106, 49909], #[106, 49803], #[106, 49697], #[106, 49591], #[106, 49485],
    #[106, 49379], #[106, 49273], #[106, 49167], #[106, 49061], #[106, 48955], #[106, 48849],
    #[106, 48743], #[106, 48637], #[106, 48531], #[106, 48425], #[106, 48319], #[106, 48213],
    #[106, 48107], #[106, 48001], #[106, 47895], #[106, 47789], #[106, 47683], #[106, 47577],
    #[106, 47471], #[106, 47365], #[106, 47259], #[106, 47153], #[106, 47047], #[106, 46941],
    #[106, 46835], #[106, 46729], #[106, 46623], #[106, 46517], #[106, 46411], #[106, 46305],
    #[106, 46199], #[106, 46093], #[106, 45987], #[106, 45881], #[106, 45775], #[106, 45669],
    #[106, 45563], #[106, 45457], #[106, 45351], #[106, 45245], #[106, 45139], #[106, 45033],
    #[106, 44927], #[106, 44821], #[106, 44715], #[106, 44609], #[106, 44503], #[106, 44397],
    #[106, 44291], #[106, 44185], #[106, 44079], #[106, 43973], #[106, 43867], #[106, 43761],
    #[106, 43655], #[106, 43549], #[106, 43443], #[106, 43337], #[106, 43231], #[106, 43125],
    #[106, 43019], #[106, 42913], #[106, 42807], #[106, 42701], #[106, 42595], #[106, 42489],
    #[106, 42383], #[106, 42277], #[106, 42171], #[106, 42065], #[106, 41959], #[106, 41853],
    #[106, 41747], #[106, 41641], #[106, 41535], #[106, 41429], #[106, 41323], #[106, 41217],
    #[106, 41111], #[106, 41005], #[106, 40899], #[106, 40793], #[106, 40687], #[106, 40581],
    #[106, 40475], #[106, 40369], #[106, 40263], #[106, 40157], #[106, 40051], #[106, 39945],
    #[106, 39839]]

set_option maxHeartbeats 0 in
-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow597Part1_checked :
    weightedGroupBaseCheck 70 47 500 1 primeSeed373Row14 target028TwoLow597Part1Base = true ∧
      weightedGroupRowsCheck 1 target028TwoLow597Part1Base target028TwoLow597Part1Row
          target028TwoLow597Part1Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow597Part1_count :
    51393 ≤ weightedPrimeCount id (List.replicate 109 70 ++ primeSeed373Weights) 117 := by
  have h :=
    target028_group_grid_general 70 47 1 109 (by decide) (by decide) target028TwoLow597Part1Base
      target028TwoLow597Part1Row target028TwoLow597Part1Rows (by decide)
      target028TwoLow597Part1_checked.1 target028TwoLow597Part1_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
