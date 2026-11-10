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

/-- The sampled base row for budget 121. -/
def target028TwoLow607Part1Base : Array ℕ :=
  #[156, 53657]

/-- The final low-group count row for budget 121. -/
def target028TwoLow607Part1Row : Array ℕ :=
  #[156, 70661]

/-- Intermediate rows for budget 121. -/
def target028TwoLow607Part1Rows : List (Array ℕ) :=
  [#[156, 70505], #[156, 70349], #[156, 70193], #[156, 70037], #[156, 69881], #[156, 69725],
    #[156, 69569], #[156, 69413], #[156, 69257], #[156, 69101], #[156, 68945], #[156, 68789],
    #[156, 68633], #[156, 68477], #[156, 68321], #[156, 68165], #[156, 68009], #[156, 67853],
    #[156, 67697], #[156, 67541], #[156, 67385], #[156, 67229], #[156, 67073], #[156, 66917],
    #[156, 66761], #[156, 66605], #[156, 66449], #[156, 66293], #[156, 66137], #[156, 65981],
    #[156, 65825], #[156, 65669], #[156, 65513], #[156, 65357], #[156, 65201], #[156, 65045],
    #[156, 64889], #[156, 64733], #[156, 64577], #[156, 64421], #[156, 64265], #[156, 64109],
    #[156, 63953], #[156, 63797], #[156, 63641], #[156, 63485], #[156, 63329], #[156, 63173],
    #[156, 63017], #[156, 62861], #[156, 62705], #[156, 62549], #[156, 62393], #[156, 62237],
    #[156, 62081], #[156, 61925], #[156, 61769], #[156, 61613], #[156, 61457], #[156, 61301],
    #[156, 61145], #[156, 60989], #[156, 60833], #[156, 60677], #[156, 60521], #[156, 60365],
    #[156, 60209], #[156, 60053], #[156, 59897], #[156, 59741], #[156, 59585], #[156, 59429],
    #[156, 59273], #[156, 59117], #[156, 58961], #[156, 58805], #[156, 58649], #[156, 58493],
    #[156, 58337], #[156, 58181], #[156, 58025], #[156, 57869], #[156, 57713], #[156, 57557],
    #[156, 57401], #[156, 57245], #[156, 57089], #[156, 56933], #[156, 56777], #[156, 56621],
    #[156, 56465], #[156, 56309], #[156, 56153], #[156, 55997], #[156, 55841], #[156, 55685],
    #[156, 55529], #[156, 55373], #[156, 55217], #[156, 55061], #[156, 54905], #[156, 54749],
    #[156, 54593], #[156, 54437], #[156, 54281], #[156, 54125], #[156, 53969], #[156, 53813],
    #[156, 53657]]

-- The finite chain checks 109 short rows.
/-- The base and low-group recurrence rows pass their checks. -/
theorem target028TwoLow607Part1_checked :
    weightedGroupBaseCheck 70 51 500 1 primeSeed373Row14 target028TwoLow607Part1Base = true ∧
      weightedGroupRowsCheck 1 target028TwoLow607Part1Base target028TwoLow607Part1Row
          target028TwoLow607Part1Rows =
        true := by
  constructor <;> decide +kernel

/-- The row lower-bounds the weighted count after the 109 low-group labels. -/
theorem target028TwoLow607Part1_count :
    70661 ≤ weightedPrimeCount id (List.replicate 109 70 ++ primeSeed373Weights) 121 := by
  have h :=
    target028_group_grid_general 70 51 1 109 (by decide) (by decide) target028TwoLow607Part1Base
      target028TwoLow607Part1Row target028TwoLow607Part1Rows (by decide)
      target028TwoLow607Part1_checked.1 target028TwoLow607Part1_checked.2
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
