/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 141, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows141Block2 : List QuarterFineWeightRow :=
  [⟨141, 37, 2, 13377, 13380, 42801, 60828, 13841277, 27224⟩,
    ⟨141, 41, 2, 12350, 12353, 41692, 64032, 15464626, 25340⟩,
    ⟨141, 43, 2, 11874, 11877, 41178, 65575, 16280291, 24482⟩,
    ⟨141, 47, 2, 10985, 10988, 40218, 68557, 17920678, 22908⟩,
    ⟨141, 49, 2, 10568, 10571, 39767, 70000, 18747403, 22186⟩,
    ⟨141, 53, 1, 9783, 9786, 38919, 72802, 20406536, 20848⟩,
    ⟨141, 59, 1, 8711, 8714, 37762, 76812, 22909582, 19074⟩,
    ⟨141, 61, 1, 8377, 8380, 37401, 78103, 23751727, 18536⟩,
    ⟨141, 64, 1, 7897, 7900, 36882, 80000, 25016992, 17776⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows141_block2_check :
    quarterFineRows141Block2.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
