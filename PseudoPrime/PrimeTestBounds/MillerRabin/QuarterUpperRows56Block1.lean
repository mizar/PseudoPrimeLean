/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block1 : List QuarterUpperWeightRow :=
  [⟨56, 17, 2, 1191, 1194, 4121, 4125, 4123, 61620832273, 39174⟩,
    ⟨56, 19, 2, 1079, 1082, 4000, 4004, 4358, 54598150017, 36044⟩,
    ⟨56, 23, 1, 888, 891, 3794, 3798, 4795, 44433780385, 30910⟩,
    ⟨56, 25, 1, 805, 808, 3704, 3708, 5000, 40609417574, 28769⟩,
    ⟨56, 27, 1, 728, 731, 3621, 3625, 5196, 37374924049, 26861⟩,
    ⟨56, 29, 1, 657, 660, 3544, 3548, 5385, 34605062955, 25143⟩,
    ⟨56, 31, 1, 590, 593, 3472, 3476, 5567, 32201080232, 23590⟩,
    ⟨56, 32, 1, 558, 561, 3437, 3441, 5656, 31093537478, 22860⟩,
    ⟨56, 37, 1, 413, 416, 3281, 3285, 6082, 26602361749, 19703⟩,
    ⟨56, 41, 0, 310, 313, 3169, 3174, 6403, 23783688760, 17628⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block1_check :
    quarterUpperRows56Block1.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
