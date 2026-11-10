/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 109, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows109Block2 : List QuarterFineWeightRow :=
  [⟨109, 37, 2, 10803, 10806, 40021, 60828, 18277216, 25695⟩,
    ⟨109, 41, 1, 9776, 9779, 38912, 64032, 20420826, 23697⟩,
    ⟨109, 43, 1, 9300, 9303, 38398, 65575, 21497900, 22792⟩,
    ⟨109, 47, 1, 8411, 8414, 37438, 68557, 23664008, 21143⟩,
    ⟨109, 49, 1, 7994, 7997, 36987, 70000, 24755687, 20390⟩,
    ⟨109, 53, 1, 7209, 7212, 36139, 72802, 26946550, 19004⟩,
    ⟨109, 59, 1, 6137, 6140, 34982, 76812, 30251787, 17183⟩,
    ⟨109, 61, 1, 5803, 5806, 34621, 78103, 31363828, 16635⟩,
    ⟨109, 64, 1, 5323, 5326, 34103, 80000, 33031289, 15861⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows109_block2_check :
    quarterFineRows109Block2.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
