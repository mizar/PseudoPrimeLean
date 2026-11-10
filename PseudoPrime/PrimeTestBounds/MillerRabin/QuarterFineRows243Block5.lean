/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block5 : List QuarterFineWeightRow :=
  [⟨243, 137, 1, 5729, 5732, 34541, 117047, 31615745, 11061⟩,
    ⟨243, 139, 1, 5584, 5587, 34384, 117899, 32116029, 10904⟩,
    ⟨243, 149, 1, 4890, 4893, 33635, 122066, 34613898, 10166⟩,
    ⟨243, 151, 1, 4756, 4759, 33490, 122883, 35119455, 10028⟩,
    ⟨243, 157, 1, 4367, 4370, 33070, 125300, 36625886, 9629⟩,
    ⟨243, 163, 1, 3992, 3995, 32665, 127672, 38139682, 9252⟩,
    ⟨243, 167, 1, 3749, 3752, 32403, 129229, 39152147, 9012⟩,
    ⟨243, 169, 1, 3630, 3633, 32274, 130000, 39660482, 8897⟩,
    ⟨243, 173, 0, 3396, 3399, 32021, 131530, 40676693, 8671⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block5_check :
    quarterFineRows243Block5.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
