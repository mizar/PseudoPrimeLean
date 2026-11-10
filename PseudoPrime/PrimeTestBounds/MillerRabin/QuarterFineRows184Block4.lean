/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 184, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows184Block4 : List QuarterFineWeightRow :=
  [⟨184, 103, 1, 5801, 5804, 34619, 101489, 31370102, 12800⟩,
    ⟨184, 107, 1, 5420, 5423, 34207, 103441, 32689544, 12328⟩,
    ⟨184, 109, 1, 5234, 5237, 34006, 104404, 33353251, 12100⟩,
    ⟨184, 113, 1, 4874, 4877, 33618, 106302, 34672791, 11664⟩,
    ⟨184, 121, 1, 4190, 4193, 32879, 110000, 37332164, 10860⟩,
    ⟨184, 125, 1, 3865, 3868, 32528, 111804, 38665791, 10488⟩,
    ⟨184, 127, 1, 3706, 3709, 32356, 112695, 39336595, 10309⟩,
    ⟨184, 128, 1, 3628, 3631, 32272, 113138, 39668414, 10221⟩,
    ⟨184, 131, 0, 3396, 3399, 32021, 114456, 40676693, 9964⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows184_block4_check :
    quarterFineRows184Block4.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
