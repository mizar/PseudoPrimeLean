/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ElevenCount

/-! # Eleven-prime weighted count through budget seventy-three -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Cumulative counts through budget 73 for eleven supplied primes. -/
def quarterElevenRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 18,
    19, 22, 24, 26, 29, 33, 35, 38, 41, 44, 48, 53, 58, 62, 67, 72, 79, 84, 92, 99, 106, 115, 125,
    134, 144, 156, 167, 179, 193, 208, 223, 239, 256, 275, 294, 315, 338, 360, 385, 412, 440, 468,
    500, 531]

/-- Suffix rows for the eleven-prime weighted recurrence through 73. -/
def quarterElevenTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 9, 10,
      11, 12, 13, 15, 17, 17, 19, 19, 20, 22, 24, 25, 27, 29, 31, 35, 36, 39, 41, 44, 48, 53, 55,
      60, 64, 68, 73, 78, 83, 89, 95, 100, 108, 115, 122, 130, 137, 146, 156, 165, 174, 185, 193],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 7,
      7, 8, 8, 10, 11, 11, 12, 12, 12, 13, 14, 14, 15, 16, 16, 18, 19, 20, 22, 24, 26, 29, 30, 33,
      35, 37, 38, 42, 44, 48, 51, 52, 55, 60, 62, 66, 69, 73, 78, 82, 85, 90, 93],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 5, 6,
      6, 7, 7, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 12, 12, 13, 14, 16, 16, 18, 19, 21, 23, 25,
      25, 28, 30, 33, 35, 36, 37, 41, 42, 44, 45, 47, 49, 52, 52, 55, 56],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 5,
      5, 6, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 10, 10, 11, 12, 13, 14, 16, 16, 19,
      21, 23, 25, 26, 27, 30, 31, 32, 33, 34, 35, 36, 36, 37, 37],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4,
      4, 5, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 9, 10, 10, 12, 13, 15,
      17, 18, 19, 22, 23, 24, 25, 26, 27, 28, 28, 28, 28],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3,
      3, 4, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 8, 9, 10,
      11, 12, 15, 16, 17, 18, 19, 20, 21, 21, 21, 21],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6,
      7, 7, 9, 10, 11, 12, 13, 14, 15, 15, 15, 15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 5, 5, 6, 7, 8, 9, 10, 10, 10, 10],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 4, 5, 6, 6, 6, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The tabulated suffix counts satisfy the weighted recurrence through 73. -/
theorem quarter_eleven_checked :
    weightedPrimeTableCheck 73 target028ElevenWeights (quarterElevenRow :: quarterElevenTail) =
      true := by
  decide +kernel

/-- The weighted family has the cardinality given by the checked table. -/
theorem quarter_eleven_family_card (H : ℕ) (hH : H ≤ 73) :
    (weightedPrimeFamily target028ElevenPrimes.toFinset target028ElevenWeight H).card =
      quarterElevenRow.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target028ElevenWeight H target028ElevenPrimes
        target028ElevenWeights target028Eleven_labels.1 target028Eleven_labels.2.2
        target028Eleven_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 73 target028ElevenWeights quarterElevenRow quarterElevenTail
        quarter_eleven_checked H hH).symm)

end PseudoPrime.PrimeTestBounds.MillerRabin
