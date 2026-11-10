/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 58, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows58Block1 : List QuarterFineWeightRow :=
  [⟨58, 16, 2, 12877, 12880, 42261, 40000, 14609255, 41009⟩,
    ⟨58, 17, 2, 12271, 12274, 41606, 41232, 15598196, 39288⟩,
    ⟨58, 19, 2, 11159, 11162, 40405, 43589, 17588675, 36197⟩,
    ⟨58, 23, 1, 9248, 9251, 38342, 47959, 21618626, 31111⟩,
    ⟨58, 25, 1, 8414, 8417, 37441, 50000, 23656910, 28994⟩,
    ⟨58, 27, 1, 7645, 7648, 36610, 51962, 25706793, 27100⟩,
    ⟨58, 29, 1, 6930, 6933, 35838, 53852, 27769971, 25391⟩,
    ⟨58, 31, 1, 6263, 6266, 35118, 55678, 29843148, 23844⟩,
    ⟨58, 32, 1, 5946, 5949, 34775, 56569, 30884525, 23126⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows58_block1_check :
    quarterFineRows58Block1.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
