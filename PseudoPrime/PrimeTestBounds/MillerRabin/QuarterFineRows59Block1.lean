/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 59, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows59Block1 : List QuarterFineWeightRow :=
  [⟨59, 16, 2, 13048, 13051, 42446, 40000, 14341469, 41145⟩,
    ⟨59, 17, 2, 12442, 12445, 41791, 41232, 15312282, 39432⟩,
    ⟨59, 19, 2, 11329, 11332, 40589, 43589, 17268003, 36352⟩,
    ⟨59, 23, 1, 9419, 9422, 38526, 47959, 21224480, 31286⟩,
    ⟨59, 25, 1, 8585, 8588, 37626, 50000, 23223281, 29172⟩,
    ⟨59, 27, 1, 7816, 7819, 36795, 51962, 25235589, 27281⟩,
    ⟨59, 29, 1, 7101, 7104, 36023, 53852, 27260950, 25575⟩,
    ⟨59, 31, 1, 6434, 6437, 35302, 55678, 29299055, 24031⟩,
    ⟨59, 32, 1, 6117, 6120, 34960, 56569, 30318414, 23311⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows59_block1_check :
    quarterFineRows59Block1.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
