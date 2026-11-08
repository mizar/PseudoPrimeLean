/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028Fine59Supply
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount

/-! # Fine weighted prime supply through 61 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Add 61 to the prime labels already certified through 59. -/
def target028Fine61Primes : List ℕ :=
  61 :: target028Fine59Primes

/-- Give 61 the rounded weight 243 and retain all existing weights. -/
def target028Fine61Weight (p : ℕ) : ℕ :=
  if p = 61 then 243 else target028Fine59Weight p

/-- Ordered weights for the supply through 61 at scale 59. -/
def target028Fine61Weights : List ℕ :=
  243 :: target028Fine59Weights

/-- The extended supply is duplicate-free, with positive matching weights. -/
theorem target028_fine61_labels :
    target028Fine61Primes.Nodup ∧
      target028Fine61Primes.map target028Fine61Weight = target028Fine61Weights ∧
      ∀ p ∈ target028Fine61Primes, 0 < target028Fine61Weight p := by
  decide +kernel

/-- Every extended label is prime, at most 61, and has a certified upper
logarithmic weight. The original supply handles all labels other than 61. -/
theorem target028_fine61_supply (p : ℕ) (hp : p ∈ target028Fine61Primes) :
    p.Prime ∧ p ≤ 61 ∧ Real.log p ≤ (target028Fine61Weight p : ℝ) / 59 := by
  simp only [target028Fine61Primes, List.mem_cons] at hp
  rcases hp with rfl | hp
  · have hlog :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 61 6 24 0 (243 / 59) = true from by
            decide +kernel)).2
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
    exact
      ⟨by decide, by decide, by
        simpa only [target028Fine61Weight, ite_true, Nat.cast_ofNat] using hlog⟩
  · have h := target028_fine59_supply p hp
    have hpne : p ≠ 61 := Nat.ne_of_lt (lt_of_le_of_lt h.2.1 (by decide))
    exact
      ⟨h.1, h.2.1.trans (by decide), by
        simpa only [target028Fine61Weight, ite_eq_right hpne] using h.2.2⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
