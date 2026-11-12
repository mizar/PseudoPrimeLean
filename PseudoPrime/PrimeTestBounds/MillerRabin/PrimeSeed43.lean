/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCount
import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Weight
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Weighted prime supply through 43 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The cumulative weighted-count row through budget 77. -/
private def primeSeed43Row : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 24, 26, 28, 33, 34, 38, 44, 47, 50, 55, 61, 64, 70, 77, 84, 89, 97, 107, 114, 122, 136,
    144, 154, 169, 183, 195, 210, 229, 246, 263, 285, 307, 327, 352, 380, 406, 436, 469, 505, 537,
    577, 621, 659, 704, 759, 809]

/-- The remaining cumulative-count rows through budget 77. -/
private def primeSeed43Tail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 12, 13, 14, 17, 17, 19, 22, 23, 24, 27, 28, 30, 32, 33, 37, 39, 42, 46, 50, 52, 59, 60,
      65, 72, 76, 81, 88, 93, 102, 109, 116, 124, 132, 142, 151, 160, 173, 184, 198, 210, 225, 241,
      253, 268, 290, 304],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 8, 8, 9, 11, 11, 12, 15, 15, 16, 17, 17, 18, 19, 19, 20, 22, 23, 24, 27, 28, 32, 32, 35,
      40, 43, 44, 49, 51, 56, 59, 64, 65, 72, 77, 79, 84, 92, 96, 105, 108, 116, 125, 129, 136, 148,
      153],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 7, 7, 7, 9, 9, 9, 12, 12, 13, 13, 13, 13, 14, 14, 15, 15, 16, 16, 19, 19, 21, 21, 23, 25,
      28, 28, 32, 34, 38, 40, 45, 45, 50, 54, 55, 57, 64, 64, 73, 73, 76, 82, 85, 87, 97, 97],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 6, 6, 6, 8, 8, 8, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 13, 13, 14, 14, 16, 16,
      19, 19, 20, 22, 25, 27, 32, 32, 36, 40, 40, 42, 48, 48, 54, 54, 55, 61, 62, 62, 69, 69],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 5, 5, 5, 7, 7, 7, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11,
      13, 13, 14, 14, 17, 19, 21, 21, 25, 29, 29, 31, 37, 37, 43, 43, 43, 49, 49, 49, 55, 55],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 4, 4, 4, 6, 6, 6, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12,
      14, 14, 15, 19, 19, 21, 27, 27, 33, 33, 33, 39, 39, 39, 45, 45],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 3, 5, 5, 5, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9,
      10, 10, 11, 13, 13, 15, 18, 18, 24, 24, 24, 30, 30, 30, 36, 36],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 4, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 8, 8, 8, 10, 10, 10, 16, 16, 16, 22, 22, 22, 28, 28],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 9, 9, 9, 15, 15, 15, 21, 21],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 9, 9, 9, 15, 15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 10, 10],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the recurrence for all weights and budgets. -/
private theorem primeSeed43_checked :
    weightedPrimeTableCheck 77 primeSeed43Weights (primeSeed43Row :: primeSeed43Tail) = true := by
  decide +kernel

/-- The weighted multiset family through budget 77 has exactly 809 members.
The table and label-invariance theorem provide its cardinality. -/
theorem primeSeed43_family_card :
    (weightedPrimeFamily primeSeed43Primes.toFinset primeSeed43Weight 77).card = 809 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed43Weight 77 primeSeed43Primes primeSeed43Weights
          primeSeed43_labels.1 primeSeed43_labels.2.2 primeSeed43_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 77 primeSeed43Weights primeSeed43Row primeSeed43Tail
          primeSeed43_checked 77 (by decide)).symm)
  change (weightedPrimeFamily primeSeed43Primes.toFinset primeSeed43Weight 77).card = 809 at h
  exact h

/-- The weighted count through 43 at budget 77 is at least 809. -/
theorem primeSeed43_count_77 : 809 ≤ weightedPrimeCount id primeSeed43Weights 77 := by
  have h :=
    weightedPrimeTableCheck_sound 77 primeSeed43Weights primeSeed43Row primeSeed43Tail
      primeSeed43_checked 77 (by decide)
  change 809 = weightedPrimeCount id primeSeed43Weights 77 at h
  exact h.le

end PseudoPrime.PrimeTestBounds.MillerRabin
