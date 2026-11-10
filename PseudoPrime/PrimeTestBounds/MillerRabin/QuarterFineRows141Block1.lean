/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 141, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows141Block1 : List QuarterFineWeightRow :=
  [⟨141, 16, 3, 21760, 21763, 51855, 40000, 5597137, 43702⟩,
    ⟨141, 17, 3, 21154, 21157, 51200, 41232, 5976022, 42480⟩,
    ⟨141, 19, 3, 20042, 20045, 49999, 43589, 6738620, 40240⟩,
    ⟨141, 23, 3, 18131, 18134, 47935, 47959, 8283414, 36413⟩,
    ⟨141, 25, 2, 17297, 17300, 47034, 50000, 9064405, 34761⟩,
    ⟨141, 27, 2, 16528, 16531, 46204, 51962, 9848855, 33246⟩,
    ⟨141, 29, 2, 15813, 15816, 45432, 53852, 10639306, 31852⟩,
    ⟨141, 31, 2, 15146, 15149, 44711, 55678, 11434730, 30568⟩,
    ⟨141, 32, 2, 14829, 14832, 44369, 56569, 11832562, 29959⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows141_block1_check :
    quarterFineRows141Block1.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
