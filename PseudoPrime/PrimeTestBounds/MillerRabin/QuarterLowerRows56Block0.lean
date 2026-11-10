/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Principal lower rows at cutoff 56, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational lower-weight certificates for a block of prime powers. -/
def quarterLowerRows56Block0 : List Target028GeneralWeightRow :=
  [⟨56, 2, 5, 3331, 3334, 6436, 1415, 1602805, 103952⟩,
    ⟨56, 3, 4, 2925, 2928, 5998, 1733, 2483714, 92407⟩,
    ⟨56, 4, 4, 2638, 2641, 5688, 2000, 3386358, 83715⟩,
    ⟨56, 5, 3, 2414, 2417, 5446, 2237, 4313524, 76705⟩,
    ⟨56, 7, 3, 2078, 2081, 5083, 2646, 6201277, 66024⟩,
    ⟨56, 8, 3, 1944, 1947, 4938, 2829, 7168921, 61782⟩,
    ⟨56, 9, 3, 1827, 1830, 4812, 3000, 8131580, 58045⟩,
    ⟨56, 11, 2, 1626, 1629, 4595, 3317, 10102220, 51768⟩]

/-- Each listed row satisfies the rational lower-weight checks. -/
theorem quarter_lower_rows56_block0_check :
    quarterLowerRows56Block0.all Target028GeneralWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
