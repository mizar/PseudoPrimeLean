/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 184, block 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows184Block6 : List QuarterFineWeightRow :=
  [⟨184, 179, 0, 274, 277, 28650, 133791, 56983131, 6846⟩,
    ⟨184, 181, 0, 163, 166, 28530, 134537, 57671047, 6747⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows184_block6_check :
    quarterFineRows184Block6.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
