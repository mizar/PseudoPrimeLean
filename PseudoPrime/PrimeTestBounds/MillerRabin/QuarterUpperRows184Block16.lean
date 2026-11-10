/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 184, block 16 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows184Block16 : List QuarterUpperWeightRow :=
  [⟨184, 2473, 4, 2597, 2600, 27, 31, 49729, 1027367802, 1⟩,
    ⟨184, 2477, 4, 2598, 2601, 25, 30, 49769, 1025315120, 1⟩,
    ⟨184, 2503, 4, 2609, 2612, 14, 18, 50029, 1014098458, 1⟩,
    ⟨184, 2521, 4, 2616, 2619, 6, 10, 50209, 1006018036, 1⟩,
    ⟨184, 2531, 4, 2620, 2623, 2, 6, 50309, 1002002001, 1⟩,
    ⟨184, 2539, 4, 2623, 2626, (-2), 3, 50388, 998001968, 1⟩,
    ⟨184, 2543, 4, 2625, 2628, (-4), 0, 50428, 996007959, 0⟩,
    ⟨184, 2549, 4, 2627, 2630, (-6), 0, 50487, 994017934, 0⟩,
    ⟨184, 2551, 4, 2628, 2631, (-7), 0, 50507, 993024412, 0⟩,
    ⟨184, 2557, 4, 2630, 2633, (-9), 0, 50566, 991040349, 0⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows184_block16_check :
    quarterUpperRows184Block16.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
