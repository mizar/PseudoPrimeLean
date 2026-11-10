/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 141, block 13 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows141Block13 : List QuarterUpperWeightRow :=
  [⟨141, 1949, 4, 2625, 2628, (-4), 0, 44147, 996007959, 0⟩,
    ⟨141, 1951, 4, 2626, 2629, (-5), 0, 44170, 995012449, 0⟩,
    ⟨141, 1973, 4, 2637, 2640, (-17), 0, 44418, 983143655, 0⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows141_block13_check :
    quarterUpperRows141Block13.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
