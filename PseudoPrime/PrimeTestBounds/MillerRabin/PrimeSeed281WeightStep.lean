/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281Checks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Checks

/-! # Logarithmic weight extension through 281 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the logarithmic bound for the previous supply, extend it to the labels through 281.
The proof checks the new cutoffs and uses the hypothesis for earlier labels. -/
theorem primeSeed281_weight_step
    (hprev : ∀ p ∈ primeSeed199Primes, Real.log p ≤ (primeSeed199Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed281Primes, Real.log p ≤ (primeSeed281Weight p : ℝ) / 10 := by
  have h211 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 211 8 16 5 (54 / 10) = true from by
          decide +kernel)).2
  have h241 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 241 8 16 5 (55 / 10) = true from by
          decide +kernel)).2
  have h269 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 269 9 16 5 (56 / 10) = true from by
          decide +kernel)).2
  have h281 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 281 9 16 5 (57 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h211 h241 h269 h281
  intro p hp
  have hprime : p.Prime ∧ p ≤ 281 := by exact primeSeed281_prime_supply p hp
  change
    p ∈
      [281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211] ++
        primeSeed199Primes at hp
  simp only [List.mem_append] at hp
  rcases hp with hnew | hold
  · by_cases h1 : p ≤ 199
    · have hn :
        ∀ p ∈ ([281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211] : List ℕ),
          199 < p := by
        decide +kernel
      exact False.elim ((Nat.not_lt_of_ge h1) (hn p hnew))
    · by_cases h2 : p ≤ 211
      · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h2)
        simp only [primeSeed281Weight, ite_eq_right h1, ite_eq_left h2, Nat.cast_ofNat]
        norm_num only [Nat.cast_ofNat] at hl
        linarith only [hl, h211]
      · by_cases h3 : p ≤ 241
        · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h3)
          simp only [primeSeed281Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
            Nat.cast_ofNat]
          norm_num only [Nat.cast_ofNat] at hl
          linarith only [hl, h241]
        · by_cases h4 : p ≤ 269
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h4)
            simp only [primeSeed281Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_left h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h269]
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
            simp only [primeSeed281Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_right h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h281]
  · have hp199 := (primeSeed199_prime_supply p hold).2
    simpa only [primeSeed281Weight, ite_eq_left hp199, primeSeed199Weight] using hprev p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
