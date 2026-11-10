/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 7 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block7 : List QuarterFineWeightRow :=
  [⟨243, 229, 0, 592, 595, 28993, 151328, 55061749, 6207⟩,
    ⟨243, 233, 0, 419, 422, 28806, 152644, 56101092, 6071⟩,
    ⟨243, 239, 0, 164, 167, 28531, 154597, 57665281, 5872⟩,
    ⟨243, 241, 0, 81, 84, 28441, 155242, 58186611, 5808⟩,
    ⟨243, 243, 0, (-1), 1, 28352, 155885, 58706783, 5746⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block7_check :
    quarterFineRows243Block7.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
