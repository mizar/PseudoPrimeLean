/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal lower rows at cutoff 56, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Fine rational lower-weight certificates for a block of prime powers. -/
def quarterFineRows56Block1 : List QuarterFineWeightRow :=
  [⟨56, 13, 2, 14603, 14606, 44125, 36056, 12124828, 46854⟩,
    ⟨56, 16, 2, 12526, 12529, 41882, 40000, 15173572, 40717⟩,
    ⟨56, 17, 2, 11920, 11923, 41227, 41232, 16200713, 38980⟩,
    ⟨56, 19, 2, 10808, 10811, 40026, 43589, 18268080, 35864⟩,
    ⟨56, 23, 1, 8897, 8900, 37962, 47959, 22455942, 30749⟩,
    ⟨56, 25, 1, 8063, 8066, 37062, 50000, 24570714, 28620⟩,
    ⟨56, 27, 1, 7294, 7297, 36231, 51962, 26699778, 26719⟩,
    ⟨56, 29, 1, 6579, 6582, 35459, 53852, 28842652, 25006⟩]

/-- Each listed row satisfies the rational lower-weight checks. -/
theorem quarter_fine_rows56_block1_check :
    quarterFineRows56Block1.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
