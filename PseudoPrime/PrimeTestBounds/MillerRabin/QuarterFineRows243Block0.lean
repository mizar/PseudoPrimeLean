/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block0 : List QuarterFineWeightRow :=
  [⟨243, 2, 7, 47998, 48001, 80192, 14143, 329083, 64287⟩,
    ⟨243, 3, 6, 43943, 43946, 75812, 17321, 509948, 61427⟩,
    ⟨243, 4, 6, 41066, 41069, 72705, 20000, 695764, 58879⟩,
    ⟨243, 5, 6, 38835, 38838, 70296, 22361, 885285, 56615⟩,
    ⟨243, 7, 5, 35470, 35473, 66661, 26458, 1273355, 52778⟩,
    ⟨243, 8, 5, 34135, 34138, 65220, 28285, 1470724, 51116⟩,
    ⟨243, 9, 5, 32957, 32960, 63947, 30000, 1670386, 49601⟩,
    ⟨243, 11, 4, 30950, 30953, 61780, 33167, 2074572, 46896⟩,
    ⟨243, 13, 4, 29280, 29283, 59976, 36056, 2484708, 44552⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block0_check :
    quarterFineRows243Block0.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
