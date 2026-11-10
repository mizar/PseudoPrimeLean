/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028NineCount

/-! # Nine-prime weighted count through budget ninety -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Cumulative counts through budget 90 for the nine supplied primes. -/
def quarterNine90Row : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 24, 26, 28, 31, 32, 36, 39, 42, 45, 50, 54, 57, 63, 67, 72, 77, 85, 90, 97, 105, 114,
    120, 130, 140, 149, 159, 171, 183, 195, 210, 224, 239, 254, 272, 288, 307, 327, 347, 368, 392,
    418, 441, 470, 497, 527, 557, 593, 626, 663, 702, 744, 784, 830, 878, 926, 976, 1031, 1088,
    1146]

/-- Suffix rows for checking the nine-prime weighted recurrence through 90. -/
def quarterNine90Tail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 12, 13, 14, 15, 15, 17, 17, 18, 19, 22, 23, 25, 27, 28, 30, 32, 35, 36, 40, 42, 47, 48,
      53, 55, 59, 62, 66, 69, 75, 80, 84, 90, 95, 101, 105, 112, 117, 123, 129, 138, 146, 153, 163,
      170, 180, 189, 201, 208, 222, 232, 247, 257, 273, 285, 300, 313, 329, 344, 362],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 8, 8, 9, 9, 9, 10, 10, 10, 11, 12, 12, 13, 14, 14, 15, 17, 18, 19, 22, 23, 25, 25, 28, 28,
      31, 32, 34, 34, 39, 40, 42, 43, 47, 48, 50, 53, 55, 57, 60, 63, 66, 69, 73, 75, 79, 84, 89,
      91, 99, 103, 109, 111, 120, 122, 130, 133, 140, 143, 154],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 11, 11, 14, 14, 16, 16, 18, 18, 21, 21,
      22, 22, 26, 26, 28, 28, 30, 30, 31, 31, 32, 32, 35, 35, 38, 38, 41, 41, 45, 45, 49, 49, 56,
      56, 61, 61, 67, 67, 73, 73, 77, 77, 85],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 8, 8, 9, 9, 11, 11, 14, 14, 15, 15,
      18, 18, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 23, 23, 24, 24, 27, 27, 30, 30, 33,
      33, 37, 37, 42, 42, 45, 45, 50],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 8, 8, 9, 9, 12, 12,
      14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 18, 18, 19,
      19, 22, 22, 24, 24, 29],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7,
      9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
      10, 10, 10, 10, 14],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4,
      5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The tabulated suffix counts satisfy the weighted recurrence through 90. -/
theorem quarter_nine90_checked :
    weightedPrimeTableCheck 90 target028NineWeights (quarterNine90Row :: quarterNine90Tail) =
      true := by
  decide +kernel

/-- The weighted family has the cardinality given by the checked table. -/
theorem quarter_nine90_family_card (H : ℕ) (hH : H ≤ 90) :
    (weightedPrimeFamily target028NinePrimes.toFinset target028NineWeight H).card =
      quarterNine90Row.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target028NineWeight H target028NinePrimes target028NineWeights
        target028Nine_labels.1 target028Nine_labels.2.2 target028Nine_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 90 target028NineWeights quarterNine90Row quarterNine90Tail
        quarter_nine90_checked H hH).symm)

end PseudoPrime.PrimeTestBounds.MillerRabin
