/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 2 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block2 : List QuarterUpperWeightRow :=
  [⟨56, 43, 0, 263, 266, 3119, 3123, 6557, 22623744567, 16689⟩,
    ⟨56, 47, 0, 174, 177, 3022, 3027, 6855, 20532315263, 15047⟩,
    ⟨56, 49, 0, 132, 135, 2977, 2981, 7000, 19628841690, 14277⟩,
    ⟨56, 53, 0, 54, 57, 2893, 2897, 7280, 18047370568, 12943⟩,
    ⟨56, 59, 0, 51, 54, 2776, 2780, 7681, 16054673630, 11221⟩,
    ⟨56, 61, 0, 84, 87, 2741, 2745, 7810, 15502479815, 10728⟩,
    ⟨56, 64, 0, 132, 135, 2689, 2693, 8000, 14716951598, 10026⟩,
    ⟨56, 67, 0, 178, 181, 2639, 2643, 8185, 13999197394, 9380⟩,
    ⟨56, 71, 0, 236, 239, 2576, 2581, 8426, 13144455033, 8618⟩,
    ⟨56, 73, 0, 264, 267, 2546, 2550, 8544, 12755977675, 8245⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block2_check :
    quarterUpperRows56Block2.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
