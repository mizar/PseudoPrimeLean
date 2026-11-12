/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SevenSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Nine-prime weighted count certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first eight supplied primes extended by the prime 23. -/
def target028NinePrimes : List ℕ :=
  primeSeed19Primes ++ [23]

/-- Logarithmic weights of the nine supplied primes, scaled by ten. -/
def target028NineWeight (p : ℕ) : ℕ :=
  if p = 23 then 32 else primeSeed19Weight p

/-- Weight list corresponding to the nine distinct prime labels. -/
def target028NineWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30, 32]

/-- The nine labels are distinct and match their positive weights. -/
theorem target028Nine_labels :
    target028NinePrimes.Nodup ∧
      target028NinePrimes.map target028NineWeight = target028NineWeights ∧
      ∀ p ∈ target028NinePrimes, 0 < target028NineWeight p := by
  decide +kernel

/-- Every listed label is prime, does not exceed 23, and satisfies its
certified scaled logarithmic weight. The first eight labels reuse the
previous supply and the final label uses a rational logarithm enclosure. -/
theorem target028Nine_supply (p : ℕ) (hp : p ∈ target028NinePrimes) :
    p.Prime ∧ p ≤ 23 ∧ Real.log p ≤ (target028NineWeight p : ℝ) / 10 := by
  have hmem : p ∈ primeSeed19Primes ∨ p = 23 := by
    simpa only [target028NinePrimes, List.mem_append, List.mem_singleton] using hp
  rcases hmem with h | h
  · have h23 : p ≠ 23 := by
      have hb := (prime_seed19_prime_supply p h).2
      exact fun he ↦ by
        subst p; norm_num only at hb
    have hb := prime_seed19_prime_supply p h
    have hw := prime_seed19_weight_bounds p h
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
