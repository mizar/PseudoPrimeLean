/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 184, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows184Block2 : List QuarterFineWeightRow :=
  [⟨184, 37, 2, 16039, 16042, 45676, 60828, 10382848, 28267⟩,
    ⟨184, 41, 2, 15012, 15015, 44567, 64032, 11600582, 26532⟩,
    ⟨184, 43, 2, 14536, 14539, 44053, 65575, 12212442, 25736⟩,
    ⟨184, 47, 2, 13646, 13649, 43091, 68557, 13445645, 24272⟩,
    ⟨184, 49, 2, 13230, 13233, 42642, 70000, 14063113, 23594⟩,
    ⟨184, 53, 2, 12445, 12448, 41794, 72802, 15307689, 22334⟩,
    ⟨184, 59, 2, 11372, 11375, 40635, 76812, 17188753, 20652⟩,
    ⟨184, 61, 2, 11039, 11042, 40276, 78103, 17817039, 20137⟩,
    ⟨184, 64, 2, 10559, 10562, 39757, 80000, 18766160, 19408⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows184_block2_check :
    quarterFineRows184Block2.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
