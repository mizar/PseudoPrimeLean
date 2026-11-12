/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Checks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281Checks

/-! # Logarithmic weight extension through 373 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the logarithmic bound for the previous supply, extend it to the labels through 373.
The proof checks the new cutoffs and uses the hypothesis for earlier labels. -/
theorem primeSeed373_weight_step
    (hprev : ∀ p ∈ primeSeed281Primes, Real.log p ≤ (primeSeed281Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed373Primes, Real.log p ≤ (primeSeed373Weight p : ℝ) / 10 := by
  have h293 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 293 9 16 5 (57 / 10) = true from by
          decide +kernel)).2
  have h317 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 317 9 16 5 (58 / 10) = true from by
          decide +kernel)).2
  have h359 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 359 9 16 5 (59 / 10) = true from by
          decide +kernel)).2
  have h373 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 373 9 16 5 (60 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h293 h317 h359 h373
  intro p hp
  have hprime : p.Prime ∧ p ≤ 373 := by exact primeSeed373_prime_supply p hp
  change
    p ∈
      [373, 367, 359, 353, 349, 347, 337, 331, 317, 313, 311, 307, 293, 283] ++
        primeSeed281Primes at hp
  simp only [List.mem_append] at hp
  rcases hp with hnew | hold
  · by_cases h1 : p ≤ 281
    · have hn :
        ∀ p ∈ ([373, 367, 359, 353, 349, 347, 337, 331, 317, 313, 311, 307, 293, 283] : List ℕ),
          281 < p := by
        decide +kernel
      exact False.elim ((Nat.not_lt_of_ge h1) (hn p hnew))
    · by_cases h2 : p ≤ 293
      · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h2)
        simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_left h2, Nat.cast_ofNat]
        norm_num only [Nat.cast_ofNat] at hl
        linarith only [hl, h293]
      · by_cases h3 : p ≤ 317
        · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h3)
          simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
            Nat.cast_ofNat]
          norm_num only [Nat.cast_ofNat] at hl
          linarith only [hl, h317]
        · by_cases h4 : p ≤ 359
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h4)
            simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_left h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h359]
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
            simp only [primeSeed373Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_right h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h373]
  · have hp281 := (primeSeed281_prime_supply p hold).2
    simpa only [primeSeed373Weight, ite_eq_left hp281, primeSeed281Weight] using hprev p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
