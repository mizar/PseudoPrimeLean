/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal lower rows at cutoff 56, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Fine rational lower-weight certificates for a block of prime powers. -/
def quarterFineRows56Block0 : List QuarterFineWeightRow :=
  [⟨56, 2, 5, 33321, 33324, 64340, 14143, 1606013, 104308⟩,
    ⟨56, 3, 4, 29266, 29269, 59961, 17321, 2488438, 92764⟩,
    ⟨56, 4, 4, 26389, 26392, 56854, 20000, 3395174, 84005⟩,
    ⟨56, 5, 3, 24158, 24161, 54444, 22361, 4320431, 76996⟩,
    ⟨56, 7, 3, 20793, 20796, 50810, 26458, 6213692, 66252⟩,
    ⟨56, 8, 3, 19458, 19461, 49368, 28285, 7177529, 61989⟩,
    ⟨56, 9, 3, 18280, 18283, 48096, 30000, 8151119, 58250⟩,
    ⟨56, 11, 2, 16273, 16276, 45929, 33167, 10123457, 51961⟩]

/-- Each listed row satisfies the rational lower-weight checks. -/
theorem quarter_fine_rows56_block0_check :
    quarterFineRows56Block0.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
