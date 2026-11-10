/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 58, block 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows58Block6 : List QuarterUpperWeightRow :=
  [⟨58, 727, 4, 2527, 2530, 102, 106, 26962, 1107383471, 1⟩,
    ⟨58, 729, 4, 2530, 2533, 99, 103, 27000, 1104066298, 1⟩,
    ⟨58, 733, 4, 2535, 2538, 93, 98, 27073, 1097461732, 1⟩,
    ⟨58, 739, 4, 2543, 2546, 85, 89, 27184, 1088717065, 1⟩,
    ⟨58, 743, 4, 2549, 2552, 78, 83, 27258, 1081122658, 1⟩,
    ⟨58, 751, 4, 2559, 2562, 68, 72, 27404, 1070365307, 1⟩,
    ⟨58, 757, 4, 2567, 2570, 59, 63, 27513, 1060775238, 1⟩,
    ⟨58, 761, 4, 2573, 2576, 52, 57, 27586, 1053375741, 1⟩,
    ⟨58, 769, 4, 2583, 2586, 42, 46, 27730, 1042894478, 1⟩,
    ⟨58, 773, 4, 2588, 2591, 36, 40, 27802, 1036655845, 1⟩,
    ⟨58, 787, 4, 2606, 2609, 17, 21, 28053, 1017145321, 1⟩,
    ⟨58, 797, 4, 2619, 2622, 3, 7, 28231, 1003004504, 1⟩,
    ⟨58, 809, 4, 2634, 2637, (-13), 0, 28442, 987084105, 0⟩,
    ⟨58, 811, 4, 2636, 2639, (-16), 0, 28478, 984127291, 0⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows58_block6_check :
    quarterUpperRows58Block6.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
