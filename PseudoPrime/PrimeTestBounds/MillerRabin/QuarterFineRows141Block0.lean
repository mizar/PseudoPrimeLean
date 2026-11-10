/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 141, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows141Block0 : List QuarterFineWeightRow :=
  [⟨141, 2, 6, 42555, 42558, 74313, 14143, 592416, 79090⟩,
    ⟨141, 3, 6, 38500, 38503, 69934, 17321, 917920, 73853⟩,
    ⟨141, 4, 5, 35623, 35626, 66827, 20000, 1252391, 69526⟩,
    ⟨141, 5, 5, 33392, 33395, 64417, 22361, 1593695, 65858⟩,
    ⟨141, 7, 4, 30027, 30030, 60783, 26458, 2292069, 59877⟩,
    ⟨141, 8, 4, 28692, 28695, 59341, 28285, 2647604, 57379⟩,
    ⟨141, 9, 4, 27514, 27517, 58069, 30000, 3006736, 55127⟩,
    ⟨141, 11, 4, 25507, 25510, 55901, 33167, 3734654, 51206⟩,
    ⟨141, 13, 3, 23837, 23840, 54098, 36056, 4472534, 47878⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows141_block0_check :
    quarterFineRows141Block0.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
