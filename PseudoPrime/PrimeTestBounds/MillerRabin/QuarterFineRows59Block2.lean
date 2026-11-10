/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 59, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows59Block2 : List QuarterFineWeightRow :=
  [⟨59, 37, 1, 4665, 4668, 33392, 60828, 35465318, 20159⟩,
    ⟨59, 41, 1, 3638, 3641, 32283, 64032, 39624803, 18071⟩,
    ⟨59, 43, 0, 3162, 3165, 31769, 65575, 41714770, 17143⟩,
    ⟨59, 47, 0, 2272, 2275, 30807, 68557, 45927096, 15482⟩,
    ⟨59, 49, 0, 1856, 1859, 30358, 70000, 48036218, 14736⟩,
    ⟨59, 53, 0, 1071, 1074, 29510, 72802, 52287392, 13386⟩,
    ⟨59, 59, 0, (-1), 1, 28352, 76812, 58706783, 11661⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows59_block2_check :
    quarterFineRows59Block2.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
