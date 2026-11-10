/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 58, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows58Block0 : List QuarterFineWeightRow :=
  [⟨58, 2, 5, 33671, 33674, 64718, 14143, 1546439, 103424⟩,
    ⟨58, 3, 4, 29617, 29620, 60340, 17321, 2395891, 92173⟩,
    ⟨58, 4, 4, 26740, 26743, 57233, 20000, 3268905, 83614⟩,
    ⟨58, 5, 4, 24509, 24512, 54823, 22361, 4159751, 76750⟩,
    ⟨58, 7, 3, 21144, 21147, 51189, 26458, 5982600, 66204⟩,
    ⟨58, 8, 3, 19809, 19812, 49747, 28285, 6910591, 62011⟩,
    ⟨58, 9, 3, 18631, 18634, 48475, 30000, 7847972, 58329⟩,
    ⟨58, 11, 2, 16624, 16627, 46308, 33167, 9746958, 52127⟩,
    ⟨58, 13, 2, 14953, 14956, 44503, 36056, 11675063, 47082⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows58_block0_check :
    quarterFineRows58Block0.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
