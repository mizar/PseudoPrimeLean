/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19Data

/-! # Extended table for the first semiprime supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The full-supply row through budget 53 for the eight-prime weight list. -/
def primeSeed19Row53 : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 23, 25, 27, 30, 31, 35, 38, 40, 43, 48, 52, 54, 60, 64, 68, 73, 81, 85, 91, 99, 107,
    112]

/-- Remaining cumulative-count rows through budget 53. -/
def primeSeed19Tail53 : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 11, 12, 13, 14, 14, 16, 16, 17, 18, 21, 22, 23, 25, 26, 28, 30, 33, 33, 37, 39, 43, 44],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 11, 11, 12, 13, 13, 14, 16, 17, 17, 20, 21, 22, 22],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9, 10, 10, 13, 13, 14, 14],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 7, 7, 8, 8],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The extended table meets every finite update and base-row check. -/
theorem primeSeed19_checked53 :
    weightedPrimeTableCheck 53 primeSeed19Weights (primeSeed19Row53 :: primeSeed19Tail53) =
      true := by
  decide +kernel

/-- The extended row gives the exact weighted-family count at every budget
through 53. The table checker and label-invariance theorem transfer the finite
certificate to the multiset family on the explicit prime supply. -/
theorem primeSeed19_family53 (H : ℕ) (hH : H ≤ 53) :
    (weightedPrimeFamily primeSeed19Primes.toFinset primeSeed19Weight H).card =
      primeSeed19Row53.getD H 0 :=
  (weightedPrimeCount_weights_eq_card primeSeed19Weight H primeSeed19Primes primeSeed19Weights
        primeSeed19_labels.1 primeSeed19_labels.2.2 primeSeed19_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 53 primeSeed19Weights primeSeed19Row53 primeSeed19Tail53
        primeSeed19_checked53 H hH).symm)

end PseudoPrime.PrimeTestBounds.MillerRabin
