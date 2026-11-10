/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 109, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows109Block4 : List QuarterFineWeightRow :=
  [⟨109, 103, 0, 565, 568, 28964, 101489, 55221660, 9236⟩,
    ⟨109, 107, 0, 184, 187, 28552, 103441, 57544311, 8791⟩,
    ⟨109, 109, 0, (-1), 1, 28352, 104404, 58706783, 8579⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows109_block4_check :
    quarterFineRows109Block4.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
