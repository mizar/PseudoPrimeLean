/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Row9

/-! # Checked row of the weighted prime count -/

@[expose] public section

-- Each 456-entry array is checked independently to limit reduction size.
set_option maxRecDepth 65536

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Count row for the suffix beginning at index 8. -/
def target028Fine53Row8 : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4,
    4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7,
    7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
    9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 12,
    12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 13, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 16, 16, 16,
    16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18, 18, 18, 19, 19, 19, 19, 20, 20, 21, 21, 22, 22, 23,
    23, 23, 23, 23, 23, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 26, 27, 27, 27, 27, 28, 29, 29, 29,
    31, 31, 31, 32, 32, 32, 33, 33, 34, 34, 35, 35, 35, 35, 36, 36, 36, 36, 36, 36, 36, 36, 37, 37,
    37, 38, 39, 40, 41, 41, 41, 41, 42, 42, 42, 42, 42, 43, 43, 44, 44, 44, 44, 45, 45, 45, 45, 45,
    45, 45, 45, 45, 45, 47, 48, 48, 48, 49, 49, 50, 50, 51, 51, 51, 52, 52, 52, 52, 52, 52, 53, 53,
    53, 53, 54, 54, 54, 54, 54, 54, 55, 56, 56, 56, 57, 57, 58, 58, 59, 59, 60, 61, 61, 61, 61, 61,
    62, 63, 63, 63, 63, 64, 64, 64, 64, 64, 65, 67, 67, 67, 67]

set_option maxHeartbeats 0 in
-- This recurrence check reduces 456 entries.
/-- The checked recurrence adds the prime weight 115. -/
theorem target028_fine53_step8 :
    weightedPrimeRowCheck 115 455 target028Fine53Row9 target028Fine53Row8 = true := by
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
