/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028EightSupply

/-! # Nine-prime weighted count certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first eight supplied primes extended by the prime 23. -/
def target028NinePrimes : List ℕ :=
  target030FirstPrimes ++ [23]

/-- Logarithmic weights of the nine supplied primes, scaled by ten. -/
def target028NineWeight (p : ℕ) : ℕ :=
  if p = 23 then 32 else target030FirstWeight p

/-- Weight list corresponding to the nine distinct prime labels. -/
def target028NineWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30, 32]

/-- Cumulative weighted counts for the nine-prime supply through budget 58. -/
def target028NineRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 24, 26, 28, 31, 32, 36, 39, 42, 45, 50, 54, 57, 63, 67, 72, 77, 85, 90, 97, 105, 114,
    120, 130, 140, 149, 159, 171]

/-- Tail rows certify the recurrence for the nine-prime supply. -/
def target028NineTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 12, 13, 14, 15, 15, 17, 17, 18, 19, 22, 23, 25, 27, 28, 30, 32, 35, 36, 40, 42, 47, 48,
      53, 55, 59, 62, 66],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 8, 8, 9, 9, 9, 10, 10, 10, 11, 12, 12, 13, 14, 14, 15, 17, 18, 19, 22, 23, 25, 25, 28, 28,
      31, 32, 34],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 11, 11, 14, 14, 16, 16, 18, 18, 21, 21,
      22],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 8, 8, 9, 9, 11, 11, 14, 14, 15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 8, 8, 9],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The complete table satisfies the weighted count recurrence through 58. -/
theorem target028Nine_checked :
    weightedPrimeTableCheck 58 target028NineWeights (target028NineRow :: target028NineTail) =
      true := by
  decide +kernel

/-- The nine labels are distinct and match their positive weights. -/
theorem target028Nine_labels :
    target028NinePrimes.Nodup ∧
      target028NinePrimes.map target028NineWeight = target028NineWeights ∧
      ∀ p ∈ target028NinePrimes, 0 < target028NineWeight p := by
  decide +kernel

/-- The checked table gives the family cardinality at every budget up to 58. -/
theorem target028Nine_family_card (H : ℕ) (hH : H ≤ 58) :
    (weightedPrimeFamily target028NinePrimes.toFinset target028NineWeight H).card =
      target028NineRow.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target028NineWeight H target028NinePrimes target028NineWeights
        target028Nine_labels.1 target028Nine_labels.2.2 target028Nine_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 58 target028NineWeights target028NineRow target028NineTail
        target028Nine_checked H hH).symm)

/-- Every listed label is prime, does not exceed 23, and satisfies its
certified scaled logarithmic weight. The first eight labels reuse the
previous supply and the final label uses a rational logarithm enclosure. -/
theorem target028Nine_supply (p : ℕ) (hp : p ∈ target028NinePrimes) :
    p.Prime ∧ p ≤ 23 ∧ Real.log p ≤ (target028NineWeight p : ℝ) / 10 := by
  have hmem : p ∈ target030FirstPrimes ∨ p = 23 := by
    simpa only [target028NinePrimes, List.mem_append, List.mem_singleton] using hp
  rcases hmem with h | h
  · have h23 : p ≠ 23 := by
      have hb := (target030_first_prime_supply p h).2
      exact fun he ↦ by
        subst p; norm_num only at hb
    have hb := target030_first_prime_supply p h
    have hw := target030_first_weight_bounds p h
    simp only [target028NineWeight, ite_eq_right h23]
    exact ⟨hb.1, le_trans hb.2 (by decide), hw⟩
  · subst p
    have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 23 5 32 3 (16 / 5) = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    refine ⟨by decide, le_rfl, ?_⟩
    change Real.log (23 : ℝ) ≤ (32 : ℝ) / 10
    norm_num only
    exact hlog

end PseudoPrime.PrimeTestBounds.MillerRabin
