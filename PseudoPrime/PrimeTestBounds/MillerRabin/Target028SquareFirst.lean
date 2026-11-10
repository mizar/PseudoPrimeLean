/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeWitness

/-! # Initial weighted square-factor certificate for coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first seven prime labels are the primes at most 17. Their weights are
inherited from the certified first supply. -/
def target028FirstPrimes : List ℕ :=
  primeSeed19Primes.take 7

/-- The logarithmic weights of the first seven supplied prime labels. -/
def target028FirstWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30]

/-- The cumulative weighted-product count for the first seven primes. -/
def target028FirstRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    18, 21, 22, 24, 26, 29, 30, 33, 36, 38, 41, 45, 49, 51, 56, 60, 64, 68, 75, 79, 84, 91, 98, 103,
    110, 119, 125, 133]

/-- Tail rows certify the cumulative weighted-product recurrence. -/
def target028FirstTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9,
      10, 10, 11, 12, 13, 13, 15, 15, 16, 17, 19, 20, 21, 23, 24, 26, 27, 30, 30, 33, 35, 38, 39,
      42, 44, 46, 49],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6,
      6, 6, 6, 7, 7, 7, 8, 8, 8, 9, 10, 10, 11, 12, 12, 13, 14, 15, 15, 17, 18, 19, 19, 21, 21, 22,
      23],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 8, 8, 9, 9, 11, 11, 12, 12, 13, 13, 14, 14],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the weighted recurrence up to budget 57. -/
theorem target028First_checked :
    weightedPrimeTableCheck 57 target028FirstWeights (target028FirstRow :: target028FirstTail) =
      true := by
  decide +kernel

/-- The seven prime labels are distinct and match the certified weights. -/
theorem target028First_labels :
    target028FirstPrimes.Nodup ∧
      target028FirstPrimes.map primeSeed19Weight = target028FirstWeights ∧
      ∀ p ∈ target028FirstPrimes, 0 < primeSeed19Weight p := by
  decide +kernel

/-- The checked table gives the weighted family count at every budget up to
57. This interface supplies the subsequent square and semiprime cells. -/
theorem target028First_family_card_at (H : ℕ) (hH : H ≤ 57) :
    (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight H).card =
      target028FirstRow.getD H 0 :=
  (weightedPrimeCount_weights_eq_card primeSeed19Weight H target028FirstPrimes target028FirstWeights
        target028First_labels.1 target028First_labels.2.2 target028First_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 57 target028FirstWeights target028FirstRow target028FirstTail
        target028First_checked H hH).symm)

end PseudoPrime.PrimeTestBounds.MillerRabin
