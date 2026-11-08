/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SharpCount

/-! # Ten-prime weighted count certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Extend the sharpened nine-prime labels by the prime 29. -/
def target028TenPrimes : List ℕ :=
  target028NinePrimes ++ [29]

/-- Give 29 the scaled logarithmic weight 34 and retain earlier weights. -/
def target028TenWeight (p : ℕ) : ℕ :=
  if p = 29 then 34 else target028SharpWeight p

/-- Weight list for the ten supplied prime labels. -/
def target028TenWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 29, 30, 32, 34]

/-- Cumulative weighted-product counts through budget 66. -/
def target028TenRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 18,
    19, 22, 24, 26, 29, 32, 34, 37, 40, 43, 47, 52, 56, 60, 65, 70, 76, 81, 89, 95, 102, 111, 120,
    128, 138, 149, 159, 170, 184, 197, 211, 226, 242, 259, 276, 296, 316]

/-- Tail rows certify the ten-prime weighted-product recurrence. -/
def target028TenTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 9, 10,
      11, 12, 13, 15, 16, 16, 18, 18, 19, 21, 23, 24, 26, 28, 30, 33, 34, 37, 39, 42, 46, 50, 52,
      57, 60, 64, 68, 73, 77, 83, 88, 93, 100, 106, 112, 119],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 7,
      7, 8, 8, 10, 10, 10, 11, 11, 11, 12, 13, 13, 14, 15, 15, 17, 18, 19, 21, 23, 25, 27, 28, 31,
      32, 34, 35, 39, 40, 44, 46, 47, 50, 54, 55, 59],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 5, 6,
      6, 7, 7, 8, 8, 8, 8, 8, 8, 9, 9, 9, 9, 10, 10, 11, 11, 12, 13, 15, 15, 17, 18, 20, 21, 23, 23,
      26, 27, 30, 31, 32, 33, 36, 36, 38],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 5,
      5, 6, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 9, 9, 10, 11, 12, 13, 15, 15, 18, 19,
      21, 22, 23, 24, 26, 26, 27],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4,
      4, 5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 8, 9, 9, 11, 12, 14,
      15, 16, 17, 19, 19, 20],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3,
      3, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 8, 9,
      10, 11, 13, 13, 14],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5,
      6, 6, 8, 8, 9],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 4, 4, 5],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the weighted count recurrence through 66. -/
theorem target028Ten_checked :
    weightedPrimeTableCheck 66 target028TenWeights (target028TenRow :: target028TenTail) =
      true := by
  decide +kernel

/-- The ten prime labels are distinct and have the listed positive weights. -/
theorem target028Ten_labels :
    target028TenPrimes.Nodup ∧
      target028TenPrimes.map target028TenWeight = target028TenWeights ∧
      ∀ p ∈ target028TenPrimes, 0 < target028TenWeight p := by
  decide +kernel

/-- The checked table gives the family cardinality at any budget up to 66. -/
theorem target028Ten_card (H : ℕ) (hH : H ≤ 66) :
    (weightedPrimeFamily target028TenPrimes.toFinset target028TenWeight H).card =
      target028TenRow.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target028TenWeight H target028TenPrimes target028TenWeights
        target028Ten_labels.1 target028Ten_labels.2.2 target028Ten_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 66 target028TenWeights target028TenRow target028TenTail
        target028Ten_checked H hH).symm)

/-- Every label is prime and at most 29, and its logarithm is bounded by its
scaled weight. The new label uses a rational logarithm certificate. -/
theorem target028Ten_supply (p : ℕ) (hp : p ∈ target028TenPrimes) :
    p.Prime ∧ p ≤ 29 ∧ Real.log p ≤ (target028TenWeight p : ℝ) / 10 := by
  have hmem : p ∈ target028NinePrimes ∨ p = 29 := by
    simpa only [target028TenPrimes, List.mem_append, List.mem_singleton] using hp
  rcases hmem with h | h
  · have hb := target028Sharp_supply p h
    have h29 : p ≠ 29 := Nat.ne_of_lt (lt_of_le_of_lt hb.2.1 (by decide))
    simp only [target028TenWeight, ite_eq_right h29]
    exact ⟨hb.1, le_trans hb.2.1 (by decide), hb.2.2⟩
  · subst p
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 29 5 32 3 (17 / 5) = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    refine ⟨by decide, by decide, ?_⟩
    change Real.log (29 : ℝ) ≤ (34 : ℝ) / 10
    norm_num only
    exact hlog

end PseudoPrime.PrimeTestBounds.MillerRabin
