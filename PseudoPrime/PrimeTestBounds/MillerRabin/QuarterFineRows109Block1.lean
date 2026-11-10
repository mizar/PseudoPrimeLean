/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 109, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows109Block1 : List QuarterFineWeightRow :=
  [⟨109, 16, 3, 19186, 19189, 49075, 40000, 7390942, 43810⟩,
    ⟨109, 17, 3, 18580, 18583, 48420, 41232, 7891255, 42431⟩,
    ⟨109, 19, 3, 17468, 17471, 47219, 43589, 8898255, 39917⟩,
    ⟨109, 23, 2, 15557, 15560, 45155, 47959, 10938134, 35666⟩,
    ⟨109, 25, 2, 14723, 14726, 44255, 50000, 11968225, 33844⟩,
    ⟨109, 27, 2, 13954, 13957, 43424, 51962, 13005278, 32189⟩,
    ⟨109, 29, 2, 13239, 13242, 42652, 53852, 14049057, 30673⟩,
    ⟨109, 31, 2, 12572, 12575, 41931, 55678, 15099404, 29282⟩,
    ⟨109, 32, 2, 12255, 12258, 41589, 56569, 15624735, 28625⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows109_block1_check :
    quarterFineRows109Block1.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
