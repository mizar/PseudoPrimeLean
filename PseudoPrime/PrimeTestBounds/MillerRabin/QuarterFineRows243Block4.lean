/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block4 : List QuarterFineWeightRow :=
  [⟨243, 103, 1, 8582, 8585, 37622, 101489, 23232572, 14371⟩,
    ⟨243, 107, 1, 8201, 8204, 37211, 103441, 24207325, 13905⟩,
    ⟨243, 109, 1, 8016, 8019, 37011, 104404, 24696345, 13682⟩,
    ⟨243, 113, 1, 7655, 7658, 36621, 106302, 25678531, 13252⟩,
    ⟨243, 121, 1, 6971, 6974, 35882, 110000, 27648052, 12452⟩,
    ⟨243, 125, 1, 6646, 6649, 35531, 111804, 28635731, 12081⟩,
    ⟨243, 127, 1, 6487, 6490, 35360, 112695, 29129612, 11900⟩,
    ⟨243, 128, 1, 6409, 6412, 35275, 113138, 29378269, 11813⟩,
    ⟨243, 131, 1, 6177, 6180, 35025, 114456, 30121984, 11553⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block4_check :
    quarterFineRows243Block4.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
