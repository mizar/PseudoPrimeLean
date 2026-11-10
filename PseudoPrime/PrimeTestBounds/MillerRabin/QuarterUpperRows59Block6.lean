/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightUpperCertificate

/-! # Upper principal rows at cutoff 59, block 6 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational weight certificates for a block of prime powers. -/
def quarterUpperRows59Block6 : List QuarterUpperWeightRow :=
  [⟨59, 727, 4, 2510, 2513, 120, 125, 26962, 1127496851, 1⟩,
    ⟨59, 729, 4, 2513, 2516, 117, 121, 27000, 1124119427, 1⟩,
    ⟨59, 733, 4, 2518, 2521, 112, 116, 27073, 1118512858, 1⟩,
    ⟨59, 739, 4, 2526, 2529, 103, 107, 27184, 1108491407, 1⟩,
    ⟨59, 743, 4, 2532, 2535, 97, 101, 27258, 1101860372, 1⟩,
    ⟨59, 751, 4, 2542, 2545, 86, 90, 27404, 1089806327, 1⟩,
    ⟨59, 757, 4, 2550, 2553, 77, 81, 27513, 1080042074, 1⟩,
    ⟨59, 761, 4, 2556, 2559, 71, 75, 27586, 1073581224, 1⟩,
    ⟨59, 769, 4, 2566, 2569, 60, 64, 27730, 1061836546, 1⟩,
    ⟨59, 773, 4, 2571, 2574, 55, 59, 27802, 1056540614, 1⟩,
    ⟨59, 787, 4, 2589, 2592, 35, 39, 28053, 1035619707, 1⟩,
    ⟨59, 797, 4, 2602, 2605, 21, 25, 28231, 1021222051, 1⟩,
    ⟨59, 809, 4, 2617, 2620, 5, 9, 28442, 1005012520, 1⟩,
    ⟨59, 811, 4, 2619, 2622, 3, 7, 28478, 1003004504, 1⟩,
    ⟨59, 821, 4, 2631, 2634, (-10), 0, 28653, 990049804, 0⟩,
    ⟨59, 823, 4, 2634, 2637, (-13), 0, 28687, 987084105, 0⟩]

/-- Each listed row satisfies its rational weight checks. -/
theorem quarter_upper_rows59_block6_check :
    quarterUpperRows59Block6.all QuarterUpperWeightRow.check = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
