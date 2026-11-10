/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 243, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows243Block2 : List QuarterFineWeightRow :=
  [⟨243, 37, 3, 18820, 18823, 48679, 60828, 7689496, 28785⟩,
    ⟨243, 41, 3, 17793, 17796, 47570, 64032, 8591344, 27226⟩,
    ⟨243, 43, 2, 17317, 17320, 47056, 65575, 9044485, 26507⟩,
    ⟨243, 47, 2, 16428, 16431, 46096, 68557, 9955799, 25175⟩,
    ⟨243, 49, 2, 16011, 16014, 45646, 70000, 10414043, 24556⟩,
    ⟨243, 53, 2, 15226, 15229, 44798, 72802, 11335680, 23400⟩,
    ⟨243, 59, 2, 14154, 14157, 43640, 76812, 12727376, 21845⟩,
    ⟨243, 61, 2, 13820, 13823, 43279, 78103, 13195228, 21368⟩,
    ⟨243, 64, 2, 13340, 13343, 42761, 80000, 13896753, 20686⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows243_block2_check :
    quarterFineRows243Block2.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
