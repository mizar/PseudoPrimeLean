/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 184, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows184Block1 : List QuarterFineWeightRow :=
  [⟨184, 16, 4, 24422, 24425, 54729, 40000, 4199037, 42940⟩,
    ⟨184, 17, 3, 23816, 23819, 54075, 41232, 4482833, 41876⟩,
    ⟨184, 19, 3, 22703, 22706, 52873, 43589, 5055391, 39921⟩,
    ⟨184, 23, 3, 20793, 20796, 50810, 47959, 6213692, 36550⟩,
    ⟨184, 25, 3, 19959, 19962, 49909, 50000, 6799542, 35081⟩,
    ⟨184, 27, 3, 19189, 19192, 49078, 51962, 7388725, 33726⟩,
    ⟨184, 29, 3, 18475, 18478, 48307, 53852, 7980932, 32474⟩,
    ⟨184, 31, 3, 17808, 17811, 47586, 55678, 8577609, 31314⟩,
    ⟨184, 32, 3, 17490, 17493, 47243, 56569, 8876925, 30762⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows184_block1_check :
    quarterFineRows184Block1.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
