/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFineWeightCertificate

/-! # Fine principal rows at cutoff 184, block 3 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterFineRows184Block3 : List QuarterFineWeightRow :=
  [⟨184, 67, 1, 10101, 10104, 39263, 81854, 19716488, 18720⟩,
    ⟨184, 71, 1, 9521, 9524, 38636, 84262, 20992291, 17865⟩,
    ⟨184, 73, 1, 9243, 9246, 38336, 85441, 21631601, 17461⟩,
    ⟨184, 79, 1, 8453, 8456, 37483, 88882, 23557760, 16334⟩,
    ⟨184, 81, 1, 8203, 8206, 37213, 90000, 24202484, 15984⟩,
    ⟨184, 83, 1, 7959, 7962, 36949, 91105, 24849938, 15646⟩,
    ⟨184, 89, 1, 7261, 7264, 36196, 94340, 26793391, 14696⟩,
    ⟨184, 97, 1, 6401, 6404, 35267, 98489, 29401781, 13564⟩,
    ⟨184, 101, 1, 5997, 6000, 34830, 100499, 30715127, 13048⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_fine_rows184_block3_check :
    quarterFineRows184Block3.all QuarterFineWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
