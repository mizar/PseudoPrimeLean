/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # First low-scale weighted count certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integer weights for the eight supplied primes up to 19, including four
small seeds. Distinct primes 17 and 19 carry the same weight. -/
def target030FirstWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30]

/-- Complete cumulative-count rows through budget 43 for the first low-scale
candidate. The first row is the complete list and the last is the empty list. -/
def target030FirstRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 23, 25, 27, 30, 31, 35, 38, 40, 43, 48, 52, 54]

/-- Remaining rows of the first candidate's cumulative-count certificate. -/
def target030FirstTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 11, 12, 13, 14, 14, 16, 16, 17, 18, 21, 22, 23],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 11, 11, 12],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

/-- Full table, with the first row separated for access to its certified count. -/
def target030FirstRows : List (Array ℕ) :=
  target030FirstRow :: target030FirstTail

set_option maxRecDepth 8192 in
/-- The first candidate's table passes every positive-weight update and base
check. Kernel reduction verifies all nine rows through budget 43. -/
theorem target030FirstRows_checked :
    weightedPrimeTableCheck 43 target030FirstWeights target030FirstRows = true := by decide +kernel

/-- The first weighted candidate contains exactly 54 multisets at budget 43.
The checked table is connected to the mathematical recurrence. -/
theorem target030First_count : weightedPrimeCount id target030FirstWeights 43 = 54 := by
  have h :=
    weightedPrimeTableCheck_sound 43 target030FirstWeights target030FirstRow target030FirstTail
      target030FirstRows_checked 43 (le_refl 43)
  exact h.symm

/-- The eight primes needed by the first half-open supply cutoff. Each is
listed once, so these labels support repeated products without merging primes
that have the same logarithmic weight. -/
def target030FirstPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19]

/-- Integer logarithm weights for the first prime supply, scaled by ten. The
last group uses a common weight for 17 and 19, matching the existing supply
at cutoff 19. -/
def target030FirstWeight (p : ℕ) : ℕ :=
  if p ≤ 2 then 7
  else
    if p ≤ 3 then 11
    else
      if p ≤ 5 then 17 else if p ≤ 7 then 20 else if p ≤ 11 then 24 else if p ≤ 13 then 26 else 30

/-- The first explicit prime list has no duplicate labels and maps to the
certified weight list. Kernel reduction checks the finite list. -/
theorem target030First_labels :
    target030FirstPrimes.Nodup ∧
      target030FirstPrimes.map target030FirstWeight = target030FirstWeights ∧
      ∀ p ∈ target030FirstPrimes, 0 < target030FirstWeight p := by
  decide +kernel

/-- The weighted family over the actual primes up to 19 has cardinality 54
at budget 43. The label-invariant recurrence identifies it with the verified
finite table, retaining the two distinct labels of weight 30. -/
theorem target030First_family_card :
    (weightedPrimeFamily target030FirstPrimes.toFinset target030FirstWeight 43).card = 54 :=
  (weightedPrimeCount_weights_eq_card target030FirstWeight 43 target030FirstPrimes
        target030FirstWeights target030First_labels.1 target030First_labels.2.2
        target030First_labels.2.1).symm.trans
    target030First_count

end PseudoPrime.PrimeTestBounds.MillerRabin
