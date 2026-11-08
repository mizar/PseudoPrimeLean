/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row7

/-! # Checked row of the weighted prime count -/

@[expose] public section

-- Each 456-entry array is checked independently to limit reduction size.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Count row for the suffix beginning at index 6. -/
def target028Fine53Row6 : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7,
    8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 12, 12,
    12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 15, 15, 15, 15, 16, 16, 16, 16, 17, 17, 17, 18,
    18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19, 19, 19, 19, 20, 20, 20, 20, 20, 21, 21, 21, 22, 22,
    22, 22, 23, 23, 24, 24, 24, 24, 24, 24, 25, 25, 26, 26, 26, 27, 27, 27, 27, 27, 28, 28, 29, 29,
    29, 30, 30, 30, 31, 32, 32, 32, 33, 34, 35, 35, 35, 36, 36, 36, 37, 37, 37, 37, 37, 38, 38, 39,
    40, 41, 42, 42, 42, 42, 43, 44, 44, 44, 44, 46, 47, 47, 47, 49, 49, 50, 50, 51, 51, 53, 54, 54,
    54, 54, 54, 56, 56, 57, 57, 58, 59, 60, 60, 61, 61, 63, 63, 64, 64, 64, 66, 67, 68, 69, 70, 70,
    70, 72, 73, 74, 74, 75, 77, 77, 77, 78, 79, 81, 81, 81, 84, 84, 85, 87, 88, 89, 90, 91, 92, 93,
    95, 95, 95, 96, 99, 100, 100, 101, 103, 104, 105, 105, 107, 107, 109, 111, 112, 113, 114, 114,
    117, 117, 119, 120, 122, 124, 125, 126, 127, 129, 131, 131, 132, 133, 135, 137, 138, 139, 141,
    142, 143, 143, 145, 148, 151, 152, 153, 156, 156, 157, 159, 161, 163, 163, 165, 168, 169, 170,
    173, 174, 177, 178, 179, 180, 182, 185, 186, 187, 188, 191, 193, 194, 196, 198, 200, 201, 203,
    206, 207, 209, 212, 215, 218, 219, 219, 224, 225, 228, 230, 232, 234, 237, 239, 241, 243, 246,
    247, 250, 252, 255, 257]

set_option maxHeartbeats 0 in
-- This recurrence check reduces 456 entries.
/-- The checked recurrence adds the prime weight 65. -/
theorem target028_fine53_step6 :
    weightedPrimeRowCheck 65 455 target028Fine53Row7 target028Fine53Row6 = true := by decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
