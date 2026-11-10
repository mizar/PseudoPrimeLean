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

/-- The sampled base row for budget 127. -/
def target028TwoLow613Part1Base : Array ℕ :=
  #[284, 83430]

/-- The final low-group count row for budget 127. -/
def target028TwoLow613Part1Row : Array ℕ :=
  #[284, 114386]

/-- Intermediate rows for budget 127. -/
def target028TwoLow613Part1Rows : List (Array ℕ) :=
  [#[284, 114102], #[284, 113818], #[284, 113534], #[284, 113250], #[284, 112966], #[284, 112682],
    #[284, 112398], #[284, 112114], #[284, 111830], #[284, 111546], #[284, 111262], #[284, 110978],
    #[284, 110694], #[284, 110410], #[284, 110126], #[284, 109842], #[284, 109558], #[284, 109274],
    #[284, 108990], #[284, 108706], #[284, 108422], #[284, 108138], #[284, 107854], #[284, 107570],
    #[284, 107286], #[284, 107002], #[284, 106718], #[284, 106434], #[284, 106150], #[284, 105866],
    #[284, 105582], #[284, 105298], #[284, 105014], #[284, 104730], #[284, 104446], #[284, 104162],
    #[284, 103878], #[284, 103594], #[284, 103310], #[284, 103026], #[284, 102742], #[284, 102458],
    #[284, 102174], #[284, 101890], #[284, 101606], #[284, 101322], #[284, 101038], #[284, 100754],
    #[284, 100470], #[284, 100186], #[284, 99902], #[284, 99618], #[284, 99334], #[284, 99050],
    #[284, 98766], #[284, 98482], #[284, 98198], #[284, 97914], #[284, 97630], #[284, 97346],
    #[284, 97062], #[284, 96778], #[284, 96494], #[284, 96210], #[284, 95926], #[284, 95642],
    #[284, 95358], #[284, 95074], #[284, 94790], #[284, 94506], #[284, 94222], #[284, 93938],
    #[284, 93654], #[284, 93370], #[284, 93086], #[284, 92802], #[284, 92518], #[284, 92234],
    #[284, 91950], #[284, 91666], #[284, 91382], #[284, 91098], #[284, 90814], #[284, 90530],
    #[284, 90246], #[284, 89962], #[284, 89678], #[284, 89394], #[284, 89110], #[284, 88826],
    #[284, 88542], #[284, 88258], #[284, 87974], #[284, 87690], #[284, 87406], #[284, 87122],
    #[284, 86838], #[284, 86554], #[284, 86270], #[284, 85986], #[284, 85702], #[284, 85418],
    #[284, 85134], #[284, 84850], #[284, 84566], #[284, 84282], #[284, 83998], #[284, 83714],
    #[284, 83430]]

-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow613Part1_checked :
    weightedGroupBaseCheck 70 57 500 1 primeSeed373Row14 target028TwoLow613Part1Base = true ∧
      weightedGroupRowsCheck 1 target028TwoLow613Part1Base target028TwoLow613Part1Row
          target028TwoLow613Part1Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow613Part1_count :
    114386 ≤ weightedPrimeCount id (List.replicate 109 70 ++ primeSeed373Weights) 127 := by
  have h :=
    target028_group_grid_general 70 57 1 109 (by decide) (by decide) target028TwoLow613Part1Base
      target028TwoLow613Part1Row target028TwoLow613Part1Rows (by decide)
      target028TwoLow613Part1_checked.1 target028TwoLow613Part1_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
