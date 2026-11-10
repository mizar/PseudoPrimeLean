/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GeneralWeightCertificate

/-! # Principal lower rows at cutoff 56, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational lower-weight certificates for a block of prime powers. -/
def quarterLowerRows56Block1 : List Target028GeneralWeightRow :=
  [⟨56, 13, 2, 1459, 1462, 4414, 3606, 12106654, 46705⟩,
    ⟨56, 16, 2, 1251, 1254, 4190, 4000, 15146284, 40560⟩,
    ⟨56, 17, 2, 1191, 1194, 4125, 4124, 16163494, 38832⟩,
    ⟨56, 19, 2, 1079, 1082, 4004, 4359, 18242522, 35726⟩,
    ⟨56, 23, 1, 888, 891, 3798, 4796, 22415558, 30619⟩,
    ⟨56, 25, 1, 805, 808, 3708, 5000, 24526527, 28515⟩,
    ⟨56, 27, 1, 728, 731, 3625, 5197, 26649097, 26609⟩,
    ⟨56, 29, 1, 657, 660, 3548, 5386, 28782146, 24916⟩]

/-- Each listed row satisfies the rational lower-weight checks. -/
theorem quarter_lower_rows56_block1_check :
    quarterLowerRows56Block1.all Target028GeneralWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
