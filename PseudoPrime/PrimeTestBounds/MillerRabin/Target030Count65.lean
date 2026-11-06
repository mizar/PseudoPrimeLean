/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030FurtherCells

/-! # Extended weighted count through budget 65 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The cumulative count row for the eight-prime supply through budget 65. -/
def target030Row65 : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 23, 25, 27, 30, 31, 35, 38, 40, 43, 48, 52, 54, 60, 64, 68, 73, 81, 85, 91, 99, 107,
    112, 121, 131, 138, 147, 158, 169, 179, 193, 205, 217, 230, 246]

/-- The remaining cumulative count rows through budget 65. -/
def target030Tail65 : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 11, 12, 13, 14, 14, 16, 16, 17, 18, 21, 22, 23, 25, 26, 28, 30, 33, 33, 37, 39, 43, 44,
      48, 50, 53, 56, 59, 62, 67, 72, 74, 79, 83, 88],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 11, 11, 12, 13, 13, 14, 16, 17, 17, 20, 21, 22, 22, 25, 25, 27,
      28, 29, 29, 34, 35, 35, 36, 39, 40],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9, 10, 10, 13, 13, 14, 14, 16, 16, 18, 18, 18,
      18, 22, 22, 22, 22, 23, 23],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 7, 7, 8, 8, 10, 10, 12, 12, 12, 12,
      15, 15, 15, 15, 15, 15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 7, 7, 7, 7, 10, 10,
      10, 10, 10, 10],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6,
      6, 6, 6, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3,
      3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The extended finite table satisfies the weighted-count recurrence. -/
theorem target030Table65_checked :
    weightedPrimeTableCheck 65 target030FirstWeights (target030Row65 :: target030Tail65) =
      true := by
  decide +kernel

/-- For each budget through 65, the checked row gives the exact number of
weighted prime multisets in the first supply. The label transfer preserves
distinct primes with equal weights. -/
theorem target030_family_card65 (H : ℕ) (hH : H ≤ 65) :
    (weightedPrimeFamily target030FirstPrimes.toFinset target030FirstWeight H).card =
      target030Row65.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target030FirstWeight H target030FirstPrimes
        target030FirstWeights target030First_labels.1 target030First_labels.2.2
        target030First_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 65 target030FirstWeights target030Row65 target030Tail65
        target030Table65_checked H hH).symm)

end PseudoPrime.PrimeTestBounds.MillerRabin
