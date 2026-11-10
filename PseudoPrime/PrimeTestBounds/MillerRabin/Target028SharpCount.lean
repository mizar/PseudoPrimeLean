/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028NineCount

/-! # Nine-prime count with a sharper weight for 17 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Refine the logarithmic weight of 17 from 30 to 29, retaining all other
nine-prime weights. This closes the gap before 29 enters the prime supply. -/
def target028SharpWeight (p : ℕ) : ℕ :=
  if p = 17 then 29 else target028NineWeight p

/-- Weights of the nine prime labels after sharpening the weight of 17. -/
def target028SharpWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 29, 30, 32]

/-- Cumulative weighted counts for the sharpened supply through budget 53. -/
def target028SharpRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 18,
    19, 22, 24, 26, 28, 31, 33, 36, 39, 42, 46, 50, 54, 58, 63, 67, 73, 78, 85, 91, 98, 106, 114,
    122]

/-- Tail rows certify the sharpened weighted-product recurrence. -/
def target028SharpTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 9, 10,
      11, 12, 13, 14, 15, 15, 17, 17, 18, 20, 22, 23, 25, 27, 28, 31, 32, 35, 37, 40, 43, 47, 49],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 6, 7,
      7, 8, 8, 9, 9, 9, 10, 10, 10, 11, 12, 12, 13, 14, 14, 16, 17, 18, 20, 22, 23, 25, 26],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 5, 6,
      6, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 11, 12, 14, 14, 16, 17],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 4, 5,
      5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 8, 8, 9, 10],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4,
      4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3,
      3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The table satisfies the weighted count recurrence through budget 53. -/
theorem target028Sharp_checked :
    weightedPrimeTableCheck 53 target028SharpWeights (target028SharpRow :: target028SharpTail) =
      true := by
  decide +kernel

/-- The prime labels are distinct and match the positive sharpened weights. -/
theorem target028Sharp_labels :
    target028NinePrimes.Nodup ∧
      target028NinePrimes.map target028SharpWeight = target028SharpWeights ∧
      ∀ p ∈ target028NinePrimes, 0 < target028SharpWeight p := by
  decide +kernel

/-- The sharpened weighted-product family has cardinality 122 at budget 53. -/
theorem target028Sharp_card :
    (weightedPrimeFamily target028NinePrimes.toFinset target028SharpWeight 53).card = 122 := by
  have h :=
    (weightedPrimeCount_weights_eq_card target028SharpWeight 53 target028NinePrimes
          target028SharpWeights target028Sharp_labels.1 target028Sharp_labels.2.2
          target028Sharp_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 53 target028SharpWeights target028SharpRow target028SharpTail
          target028Sharp_checked 53 (by decide)).symm)
  change (weightedPrimeFamily target028NinePrimes.toFinset target028SharpWeight 53).card = 122 at h
  exact h

/-- Each sharpened label remains prime and at most 23, and its weight bounds
its logarithm. Only the label 17 needs a new rational logarithm certificate. -/
theorem target028Sharp_supply (p : ℕ) (hp : p ∈ target028NinePrimes) :
    p.Prime ∧ p ≤ 23 ∧ Real.log p ≤ (target028SharpWeight p : ℝ) / 10 := by
  by_cases h17 : p = 17
  · subst p
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 17 5 32 2 (29 / 10) = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    refine ⟨by decide, by decide, ?_⟩
    change Real.log (17 : ℝ) ≤ (29 : ℝ) / 10
    exact hlog
  · have h := target028Nine_supply p hp
    simp only [target028SharpWeight, ite_eq_right h17]
    exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
