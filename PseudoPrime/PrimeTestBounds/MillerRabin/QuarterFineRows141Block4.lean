/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 141, block 4 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows141Block4 : List QuarterFineWeightRow :=
  [⟨141, 103, 0, 3139, 3142, 31744, 101489, 41819188, 11061⟩,
    ⟨141, 107, 0, 2758, 2761, 31332, 103441, 43578123, 10595⟩,
    ⟨141, 109, 0, 2573, 2576, 31133, 104404, 44454014, 10371⟩,
    ⟨141, 113, 0, 2212, 2215, 30743, 106302, 46221972, 9944⟩,
    ⟨141, 121, 0, 1528, 1531, 30004, 110000, 49767157, 9162⟩,
    ⟨141, 125, 0, 1203, 1206, 29653, 111804, 51545003, 8802⟩,
    ⟨141, 127, 0, 1044, 1047, 29481, 112695, 52439245, 8630⟩,
    ⟨141, 128, 0, 966, 969, 29397, 113138, 52881590, 8545⟩,
    ⟨141, 131, 0, 734, 737, 29146, 114456, 54225716, 8299⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows141_block4_check :
    quarterFineRows141Block4.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
