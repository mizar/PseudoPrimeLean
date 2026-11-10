/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 109, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows109Block3 : List QuarterFineWeightRow :=
  [⟨109, 67, 1, 4865, 4868, 33608, 81854, 34707481, 15141⟩,
    ⟨109, 71, 1, 4285, 4288, 32982, 84262, 36949616, 14252⟩,
    ⟨109, 73, 1, 4007, 4010, 32681, 85441, 38078707, 13838⟩,
    ⟨109, 79, 0, 3218, 3221, 31829, 88882, 41465231, 12692⟩,
    ⟨109, 81, 0, 2967, 2970, 31558, 90000, 42604303, 12340⟩,
    ⟨109, 83, 0, 2724, 2727, 31296, 91105, 43735287, 12002⟩,
    ⟨109, 89, 0, 2026, 2029, 30542, 94340, 47160433, 11063⟩,
    ⟨109, 97, 0, 1165, 1168, 29612, 98489, 51756771, 9964⟩,
    ⟨109, 101, 0, 761, 764, 29176, 100499, 54063283, 9470⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows109_block3_check :
    quarterFineRows109Block3.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
