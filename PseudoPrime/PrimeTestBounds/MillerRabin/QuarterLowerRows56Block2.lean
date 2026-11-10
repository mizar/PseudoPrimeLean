/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Principal lower rows at cutoff 56, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational lower-weight certificates for a block of prime powers. -/
def quarterLowerRows56Block2 : List Target028GeneralWeightRow :=
  [⟨56, 31, 1, 590, 593, 3476, 5568, 30930887, 23363⟩,
    ⟨56, 32, 1, 558, 561, 3441, 5657, 32032636, 22653⟩,
    ⟨56, 37, 1, 413, 416, 3285, 6083, 37440585, 19502⟩,
    ⟨56, 41, 0, 310, 313, 3174, 6404, 41835919, 17421⟩,
    ⟨56, 43, 0, 263, 266, 3123, 6558, 44024895, 16513⟩,
    ⟨56, 47, 0, 174, 177, 3027, 6856, 48460802, 14868⟩,
    ⟨56, 49, 0, 132, 135, 2981, 7000, 50742066, 14138⟩,
    ⟨56, 53, 0, 54, 57, 2897, 7281, 55188537, 12807⟩]

/-- Each listed row satisfies the rational lower-weight checks. -/
theorem quarter_lower_rows56_block2_check :
    quarterLowerRows56Block2.all Target028GeneralWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
