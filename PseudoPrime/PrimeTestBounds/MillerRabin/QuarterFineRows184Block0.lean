/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 184, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows184Block0 : List QuarterFineWeightRow :=
  [⟨184, 2, 7, 45216, 45219, 77187, 14143, 444437, 71730⟩,
    ⟨184, 3, 6, 41162, 41165, 72809, 17321, 688565, 67763⟩,
    ⟨184, 4, 6, 38285, 38288, 69702, 20000, 939464, 64381⟩,
    ⟨184, 5, 5, 36053, 36056, 67291, 22361, 1195608, 61458⟩,
    ⟨184, 7, 5, 32689, 32692, 63658, 26458, 1719365, 56592⟩,
    ⟨184, 8, 5, 31353, 31356, 62215, 28285, 1986263, 54531⟩,
    ⟨184, 9, 4, 30176, 30179, 60944, 30000, 2255463, 52656⟩,
    ⟨184, 11, 4, 28169, 28172, 58776, 33167, 2801500, 49359⟩,
    ⟨184, 13, 4, 26498, 26501, 56972, 36056, 3355347, 46529⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows184_block0_check :
    quarterFineRows184Block0.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
