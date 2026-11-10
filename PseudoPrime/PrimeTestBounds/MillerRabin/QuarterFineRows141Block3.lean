/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 141, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows141Block3 : List QuarterFineWeightRow :=
  [⟨141, 67, 1, 7439, 7442, 36388, 81854, 26283865, 17061⟩,
    ⟨141, 71, 1, 6859, 6862, 35761, 84262, 27984625, 16179⟩,
    ⟨141, 73, 1, 6582, 6585, 35462, 85441, 28834000, 15763⟩,
    ⟨141, 79, 1, 5792, 5795, 34609, 88882, 31401487, 14610⟩,
    ⟨141, 81, 1, 5542, 5545, 34339, 90000, 32260877, 14254⟩,
    ⟨141, 83, 1, 5298, 5301, 34076, 91105, 33120594, 13910⟩,
    ⟨141, 89, 1, 4600, 4603, 33322, 94340, 35714446, 12952⟩,
    ⟨141, 97, 1, 3739, 3742, 32392, 98489, 39195238, 11819⟩,
    ⟨141, 101, 0, 3335, 3338, 31956, 100499, 40941952, 11305⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows141_block3_check :
    quarterFineRows141Block3.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
