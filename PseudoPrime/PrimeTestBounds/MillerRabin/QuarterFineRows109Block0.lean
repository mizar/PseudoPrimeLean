/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 109, block 0 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows109Block0 : List QuarterFineWeightRow :=
  [⟨109, 2, 6, 39981, 39984, 71533, 14143, 782278, 86310⟩,
    ⟨109, 3, 5, 35926, 35929, 67154, 17321, 1212101, 79619⟩,
    ⟨109, 4, 5, 33049, 33052, 64047, 20000, 1653766, 74236⟩,
    ⟨109, 5, 4, 30818, 30821, 61637, 22361, 2104452, 69750⟩,
    ⟨109, 7, 4, 27453, 27456, 58003, 26458, 3026646, 62565⟩,
    ⟨109, 8, 4, 26118, 26121, 56561, 28285, 3496125, 59607⟩,
    ⟨109, 9, 4, 24940, 24943, 55289, 30000, 3970354, 56960⟩,
    ⟨109, 11, 3, 22933, 22936, 53121, 33167, 4931559, 52395⟩,
    ⟨109, 13, 3, 21262, 21265, 51317, 36056, 5906510, 48563⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows109_block0_check :
    quarterFineRows109Block0.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
