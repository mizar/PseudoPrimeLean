/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ElevenCount

/-! # Refined twelve-prime weighted count -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Twelve prime labels with logarithmic weights rounded to twentieths.
The sharper weights extend the semiprime counting range. -/
def target028TwelvePrimes : List ℕ :=
  37 :: target028ElevenPrimes

/-- Rounded logarithmic weights for the twelve selected primes. -/
def target028Fine37Weight : ℕ → ℕ
  | 37 => 73
  | 2 => 14
  | 3 => 22
  | 5 => 33
  | 7 => 39
  | 11 => 48
  | 13 => 52
  | 17 => 57
  | 19 => 59
  | 23 => 63
  | 29 => 68
  | 31 => 69
  | _ => 0

/-- The checked weights of the twelve prime labels. -/
def target028Fine37Weights : List ℕ :=
  [73, 14, 22, 33, 39, 48, 52, 57, 59, 63, 68, 69]

/-- The cumulative weighted count through budget 140. -/
def target028Fine37Row : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4,
    4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 9, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 15, 16, 17, 18, 19,
    19, 21, 22, 23, 24, 24, 27, 28, 29, 31, 33, 34, 36, 38, 39, 41, 42, 44, 46, 47, 50, 53, 54, 57,
    59, 62, 64, 67, 70, 72, 75, 79, 83, 84, 88, 92, 97, 100, 103, 108, 112, 117, 122, 126, 130, 137,
    142, 147, 152, 158, 165, 171, 177, 184, 192, 198, 206, 213, 223, 230, 239, 248, 256, 265, 275,
    286, 296, 307, 317, 330, 341, 352, 367, 378, 391, 406, 420, 433, 449, 465, 483]

/-- Tail arrays certify every step of the weighted count recurrence. -/
def target028Fine37Tail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4,
      4, 5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 8, 9, 9, 9, 10, 11, 11, 12, 12, 13, 14, 14, 15, 16, 17, 18,
      19, 19, 21, 22, 23, 24, 24, 27, 28, 29, 31, 33, 34, 36, 37, 38, 40, 41, 43, 45, 46, 49, 52,
      53, 56, 58, 61, 63, 65, 68, 70, 73, 77, 81, 82, 86, 89, 94, 97, 100, 105, 109, 113, 118, 122,
      126, 133, 137, 142, 147, 152, 159, 165, 170, 177, 185, 190, 198, 204, 214, 221, 229, 237, 245,
      253, 263, 273, 282, 293, 302, 314, 324, 334, 348, 359, 370, 384, 397, 409, 425, 438, 455],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 7, 8, 8, 9, 9, 10, 10,
      11, 11, 12, 12, 12, 14, 14, 15, 16, 17, 17, 18, 18, 19, 19, 19, 20, 21, 22, 22, 24, 24, 25,
      25, 27, 27, 28, 30, 30, 32, 34, 36, 36, 37, 37, 41, 41, 42, 44, 46, 48, 50, 52, 53, 56, 56,
      60, 61, 63, 65, 68, 70, 72, 76, 77, 80, 82, 88, 88, 92, 95, 98, 101, 104, 108, 112, 116, 117,
      124, 126, 130, 134, 138, 141, 147, 152, 156, 162, 165, 173],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 7, 7, 7,
      7, 8, 8, 8, 9, 9, 10, 11, 11, 11, 12, 12, 12, 12, 12, 12, 13, 13, 13, 14, 14, 14, 14, 15, 15,
      16, 16, 16, 17, 18, 19, 19, 19, 19, 22, 22, 23, 24, 25, 26, 28, 28, 29, 31, 31, 33, 34, 35,
      35, 38, 38, 38, 40, 41, 43, 45, 47, 47, 50, 51, 52, 53, 54, 56, 59, 60, 61, 64, 65, 67, 69,
      70, 71, 75, 76, 79, 82, 83, 85],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 6, 6, 6,
      6, 7, 7, 7, 7, 7, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11,
      11, 11, 12, 12, 12, 12, 12, 14, 14, 15, 15, 16, 16, 17, 17, 18, 19, 19, 21, 22, 23, 23, 25,
      25, 25, 26, 27, 29, 31, 32, 32, 34, 35, 36, 36, 36, 37, 40, 41, 42, 42, 43, 44, 45, 45, 45,
      47, 48, 50, 51, 52, 52],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 5, 5, 5,
      5, 6, 6, 6, 6, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
      8, 8, 8, 9, 9, 9, 9, 10, 10, 10, 10, 11, 12, 12, 13, 13, 14, 14, 16, 16, 16, 17, 18, 20, 21,
      22, 22, 24, 25, 26, 26, 26, 27, 29, 30, 31, 31, 31, 32, 33, 33, 33, 33, 34, 35, 36, 36, 36],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4, 4, 4,
      4, 5, 5, 5, 5, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 10, 10, 10, 11, 12, 13, 13, 14, 14, 16,
      17, 18, 18, 18, 19, 21, 22, 23, 23, 23, 24, 25, 25, 25, 25, 26, 27, 28, 28, 28],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3,
      3, 4, 4, 4, 4, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11,
      11, 11, 12, 14, 15, 16, 16, 16, 17, 18, 18, 18, 18, 19, 20, 21, 21, 21],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2,
      2, 3, 3, 3, 3, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7,
      7, 7, 8, 9, 10, 10, 10, 11, 12, 12, 12, 12, 13, 14, 15, 15, 15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 2, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 5, 5, 5, 5, 5, 6, 7, 7, 7, 7, 8, 9, 10, 10, 10],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5, 6, 6, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

-- Reduction checks the weighted recurrence for twelve labels and 141 budgets.
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
-- The complete finite table contains thirteen arrays of 141 entries.
/-- The rational weighted count table satisfies the exact recurrence. -/
theorem target028_fine37_checked :
    weightedPrimeTableCheck 140 target028Fine37Weights (target028Fine37Row :: target028Fine37Tail) =
      true := by
  decide +kernel

/-- The prime labels are distinct and carry the listed positive weights. -/
theorem target028_fine37_labels :
    target028TwelvePrimes.Nodup ∧
      target028TwelvePrimes.map target028Fine37Weight = target028Fine37Weights ∧
      ∀ p ∈ target028TwelvePrimes, 0 < target028Fine37Weight p := by
  decide +kernel

-- Eleven logarithm intervals are checked by the finite Taylor criterion.
set_option maxRecDepth 65536 in
/-- Each refined weight is an upper bound for twenty times the prime logarithm. -/
theorem target028_fine37_log_check :
    ∀ p ∈ target028TwelvePrimes,
      Analysis.rationalLogIntervalCheck p (Nat.log2 p + 1) 24 0
          ((target028Fine37Weight p : ℚ) / 20) =
        true := by
  decide +kernel

/-- Each refined label is a prime at most 31 and satisfies its logarithmic
weight bound. The existing primality evidence and the checked logarithm
interval provide the hypotheses for weighted semiprime counting. -/
theorem target028_fine37_supply (p : ℕ) (hp : p ∈ target028TwelvePrimes) :
    p.Prime ∧ p ≤ 37 ∧ Real.log p ≤ (target028Fine37Weight p : ℝ) / 20 := by
  have h := Analysis.rationalLogIntervalCheck_sound (target028_fine37_log_check p hp)
  have hprime : p.Prime ∧ p ≤ 37 := by
    have hc : ∀ p ∈ target028TwelvePrimes, p.Prime ∧ p ≤ 37 := by decide +kernel
    exact hc p hp
  simp only [Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] at h
  exact ⟨hprime.1, hprime.2, h.2⟩

/-- The checked recurrence gives the exact weighted-family cardinality for
every budget through 140. The count-to-family theorem transfers the table. -/
theorem target028_fine37_card (H : ℕ) (hH : H ≤ 140) :
    (weightedPrimeFamily target028TwelvePrimes.toFinset target028Fine37Weight H).card =
      target028Fine37Row.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target028Fine37Weight H target028TwelvePrimes
        target028Fine37Weights target028_fine37_labels.1 target028_fine37_labels.2.2
        target028_fine37_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 140 target028Fine37Weights target028Fine37Row
        target028Fine37Tail target028_fine37_checked H hH).symm)

end PseudoPrime.PrimeTestBounds.MillerRabin
