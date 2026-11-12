/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Data
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Checks
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithmic weight extension through 1849 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the primality of the added labels and the previous logarithmic
weight bounds, extend the bounds to the supply through 1849. -/
theorem primeSeed1849_weight_step (hextra : ∀ p ∈ primeSeed1849Extra, p.Prime ∧ 373 < p ∧ p ≤ 1849)
    (hprev : ∀ p ∈ primeSeed373Primes, Real.log p ≤ (primeSeed373Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed1849Primes, Real.log p ≤ (primeSeed1849Weight p : ℝ) / 10 := by
  have hB :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1849 11 16 7 (76 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hB
  intro p hp
  change p ∈ primeSeed1849Extra ++ primeSeed373Primes at hp
  simp only [List.mem_append] at hp
  rcases hp with hnew | hold
  · have hx := hextra p hnew
    have hl := Real.log_le_log (Nat.cast_pos.mpr hx.1.pos) (Nat.cast_le.mpr hx.2.2)
    simp only [primeSeed1849Weight, ite_eq_right (Nat.not_le_of_gt hx.2.1), Nat.cast_ofNat]
    norm_num only [Nat.cast_ofNat] at hl
    linarith only [hl, hB]
  · have hp373 := (primeSeed373_prime_supply p hold).2
    simpa only [primeSeed1849Weight, ite_eq_left hp373, primeSeed373Weight] using hprev p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
