/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 58, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows58Block2 : List QuarterFineWeightRow :=
  [⟨58, 37, 1, 4494, 4497, 33207, 60828, 36127533, 19974⟩,
    ⟨58, 41, 1, 3467, 3470, 32098, 64032, 40364685, 17888⟩,
    ⟨58, 43, 0, 2991, 2994, 31584, 65575, 42493676, 16962⟩,
    ⟨58, 47, 0, 2101, 2104, 30623, 68557, 46779977, 15303⟩,
    ⟨58, 49, 0, 1685, 1688, 30174, 70000, 48928266, 14559⟩,
    ⟨58, 53, 0, 900, 903, 29326, 72802, 53258386, 13213⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows58_block2_check :
    quarterFineRows58Block2.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
