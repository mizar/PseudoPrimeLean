/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal lower rows at cutoff 56, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Fine rational lower-weight certificates for a block of prime powers. -/
def quarterFineRows56Block2 : List QuarterFineWeightRow :=
  [⟨56, 31, 1, 5912, 5915, 34739, 55678, 30995910, 23457⟩,
    ⟨56, 32, 1, 5595, 5598, 34396, 56569, 32077513, 22738⟩,
    ⟨56, 37, 1, 4143, 4146, 32828, 60828, 37523045, 19588⟩,
    ⟨56, 41, 0, 3116, 3119, 31719, 64032, 41923866, 17507⟩,
    ⟨56, 43, 0, 2640, 2643, 31205, 65575, 44135095, 16585⟩,
    ⟨56, 47, 0, 1751, 1754, 30245, 68557, 48582106, 14935⟩,
    ⟨56, 49, 0, 1334, 1337, 29794, 70000, 50823318, 14196⟩,
    ⟨56, 53, 0, 549, 552, 28947, 72802, 55315617, 12859⟩]

/-- Each listed row satisfies the rational lower-weight checks. -/
theorem quarter_fine_rows56_block2_check :
    quarterFineRows56Block2.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
