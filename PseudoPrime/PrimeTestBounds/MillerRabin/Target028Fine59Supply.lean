/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine53Suffix
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount

/-! # Fine weighted prime supply through 59 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Add 59 to the prime labels already certified through 53. -/
def target028Fine59Primes : List ℕ :=
  59 :: target028SixteenPrimes

/-- Give 59 the rounded weight 241 and retain all existing weights. -/
def target028Fine59Weight (p : ℕ) : ℕ :=
  if p = 59 then 241 else target028Fine53Weight p

/-- Ordered weights for the supply through 59 at scale 59. -/
def target028Fine59Weights : List ℕ :=
  241 :: target028Fine53Weights

/-- The extended supply is duplicate-free, with positive matching weights. -/
theorem target028_fine59_labels :
    target028Fine59Primes.Nodup ∧
      target028Fine59Primes.map target028Fine59Weight = target028Fine59Weights ∧
      ∀ p ∈ target028Fine59Primes, 0 < target028Fine59Weight p := by
  decide +kernel

/-- Every extended label is prime, at most 59, and has a certified upper
logarithmic weight. The original supply handles all labels other than 59. -/
theorem target028_fine59_supply (p : ℕ) (hp : p ∈ target028Fine59Primes) :
    p.Prime ∧ p ≤ 59 ∧ Real.log p ≤ (target028Fine59Weight p : ℝ) / 59 := by
  simp only [target028Fine59Primes, List.mem_cons] at hp
  rcases hp with rfl | hp
  · have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 59 6 24 0 (241 / 59) = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    exact
      ⟨by decide, by decide, by
        simpa only [target028Fine59Weight, ite_true, Nat.cast_ofNat] using hlog⟩
  · have h := target028_fine53_supply p hp
    have hpne : p ≠ 59 := Nat.ne_of_lt (lt_of_le_of_lt h.2.1 (by decide))
    exact
      ⟨h.1, h.2.1.trans (by decide), by
        simpa only [target028Fine59Weight, ite_eq_right hpne] using h.2.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
