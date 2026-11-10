/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Principal upper rows at cutoff 56, block 15 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational upper-weight certificates for a block of prime powers. -/
def quarterUpperRows56Block15 : List QuarterUpperWeightRow :=
  [⟨56, 727, 4, 2562, 2565, 64, 69, 26962, 1066092397, 1⟩,
    ⟨56, 729, 4, 2565, 2568, 61, 65, 27000, 1062898913, 1⟩,
    ⟨56, 733, 4, 2570, 2573, 56, 60, 27073, 1057597682, 1⟩,
    ⟨56, 739, 4, 2578, 2581, 47, 51, 27184, 1048122007, 1⟩,
    ⟨56, 743, 4, 2584, 2587, 41, 45, 27258, 1041852103, 1⟩,
    ⟨56, 751, 4, 2595, 2598, 29, 33, 27404, 1029424593, 1⟩,
    ⟨56, 757, 4, 2603, 2606, 20, 24, 27513, 1020201339, 1⟩,
    ⟨56, 761, 4, 2608, 2611, 15, 19, 27586, 1015113064, 1⟩,
    ⟨56, 769, 4, 2618, 2621, 4, 8, 27730, 1004008010, 1⟩,
    ⟨56, 773, 4, 2623, 2626, (-2), 3, 27802, 998001968, 1⟩]

/-- Each listed row satisfies the rational upper-weight checks. -/
theorem quarter_upper_rows56_block15_check :
    quarterUpperRows56Block15.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
