/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 1 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block1 : List QuarterFineWeightRow :=
  [⟨243, 16, 4, 27203, 27206, 57733, 40000, 3109479, 41536⟩,
    ⟨243, 17, 4, 26597, 26600, 57078, 41232, 3319968, 40638⟩,
    ⟨243, 19, 4, 25485, 25488, 55878, 43589, 3743253, 38970⟩,
    ⟨243, 23, 3, 23574, 23577, 53814, 47959, 4601375, 36070⟩,
    ⟨243, 25, 3, 22740, 22743, 52913, 50000, 5035210, 34795⟩,
    ⟨243, 27, 3, 21971, 21974, 52082, 51962, 5471513, 33615⟩,
    ⟨243, 29, 3, 21256, 21259, 51310, 53852, 5910646, 32517⟩,
    ⟨243, 31, 3, 20589, 20592, 50590, 55678, 6351908, 31491⟩,
    ⟨243, 32, 3, 20272, 20275, 50247, 56569, 6573558, 31006⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block1_check :
    quarterFineRows243Block1.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
