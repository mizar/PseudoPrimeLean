/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TenCount

/-! # Eleven-prime weighted count certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Extend the ten-prime labels by the prime 31. -/
def target028ElevenPrimes : List ℕ :=
  target028TenPrimes ++ [31]

/-- Give 31 the scaled logarithmic weight 35 and retain earlier weights. -/
def target028ElevenWeight (p : ℕ) : ℕ :=
  if p = 31 then 35 else target028TenWeight p

/-- Weight list for the ten supplied prime labels. -/
def target028ElevenWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 29, 30, 32, 34, 35]

/-- Cumulative weighted-product counts through budget 66. -/
def target028ElevenRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 18,
    19, 22, 24, 26, 29, 33, 35, 38, 41, 44, 48, 53, 58, 62, 67, 72, 79, 84, 92, 99, 106, 115, 125,
    134, 144, 156, 167, 179, 193, 208, 223, 239, 256, 275, 294, 315, 338]

/-- Tail rows certify the eleven-prime recurrence. -/
def target028ElevenTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 9, 10,
      11, 12, 13, 15, 17, 17, 19, 19, 20, 22, 24, 25, 27, 29, 31, 35, 36, 39, 41, 44, 48, 53, 55,
      60, 64, 68, 73, 78, 83, 89, 95, 100, 108, 115, 122, 130],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 7,
      7, 8, 8, 10, 11, 11, 12, 12, 12, 13, 14, 14, 15, 16, 16, 18, 19, 20, 22, 24, 26, 29, 30, 33,
      35, 37, 38, 42, 44, 48, 51, 52, 55, 60, 62, 66],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 5, 6,
      6, 7, 7, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 11, 11, 12, 12, 13, 14, 16, 16, 18, 19, 21, 23, 25,
      25, 28, 30, 33, 35, 36, 37, 41, 42, 44],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 5,
      5, 6, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9, 10, 10, 11, 12, 13, 14, 16, 16, 19,
      21, 23, 25, 26, 27, 30, 31, 32],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4,
      4, 5, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 9, 10, 10, 12, 13, 15,
      17, 18, 19, 22, 23, 24],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3,
      3, 4, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 8, 9, 10,
      11, 12, 15, 16, 17],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6,
      7, 7, 9, 10, 11],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 5, 5, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the weighted count recurrence through 66. -/
theorem target028Eleven_checked :
    weightedPrimeTableCheck 66 target028ElevenWeights (target028ElevenRow :: target028ElevenTail) =
      true := by
  decide +kernel

/-- The eleven prime labels are distinct and have the listed positive weights. -/
theorem target028Eleven_labels :
    target028ElevenPrimes.Nodup ∧
      target028ElevenPrimes.map target028ElevenWeight = target028ElevenWeights ∧
      ∀ p ∈ target028ElevenPrimes, 0 < target028ElevenWeight p := by
  decide +kernel

/-- The checked table gives the family cardinality at any budget up to 66. -/
theorem target028Eleven_card (H : ℕ) (hH : H ≤ 66) :
    (weightedPrimeFamily target028ElevenPrimes.toFinset target028ElevenWeight H).card =
      target028ElevenRow.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target028ElevenWeight H target028ElevenPrimes
        target028ElevenWeights target028Eleven_labels.1 target028Eleven_labels.2.2
        target028Eleven_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 66 target028ElevenWeights target028ElevenRow target028ElevenTail
        target028Eleven_checked H hH).symm)

/-- Every label is prime, at most 31, and has a certified logarithmic weight. -/
theorem target028Eleven_supply (p : ℕ) (hp : p ∈ target028ElevenPrimes) :
    p.Prime ∧ p ≤ 31 ∧ Real.log p ≤ (target028ElevenWeight p : ℝ) / 10 := by
  have hmem : p ∈ target028TenPrimes ∨ p = 31 := by
    simpa only [target028ElevenPrimes, List.mem_append, List.mem_singleton] using hp
  rcases hmem with h | h
  · have hb := target028Ten_supply p h
    have h31 : p ≠ 31 := Nat.ne_of_lt (lt_of_le_of_lt hb.2.1 (by decide))
    simp only [target028ElevenWeight, ite_eq_right h31]
    exact ⟨hb.1, le_trans hb.2.1 (by decide), hb.2.2⟩
  · subst p
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 31 5 32 3 (7 / 2) = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    refine ⟨by decide, by decide, ?_⟩
    change Real.log (31 : ℝ) ≤ (35 : ℝ) / 10
    norm_num only
    exact hlog

end PseudoPrime.PrimeTestBounds.MillerRabin
