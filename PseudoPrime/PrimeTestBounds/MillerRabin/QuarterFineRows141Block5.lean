/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 141, block 5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows141Block5 : List QuarterFineWeightRow :=
  [⟨141, 137, 0, 286, 289, 28663, 117047, 56909101, 7833⟩,
    ⟨141, 139, 0, 141, 144, 28506, 117899, 57809624, 7686⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows141_block5_check :
    quarterFineRows141Block5.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
