/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Checks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Checks

/-! # Logarithmic weight extension through 199 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the logarithmic bound for the previous supply, extend it to the labels through 199.
The proof checks the new cutoffs and uses the hypothesis for earlier labels. -/
theorem primeSeed199_weight_step
    (hprev : ∀ p ∈ primeSeed113Primes, Real.log p ≤ (primeSeed113Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed199Primes, Real.log p ≤ (primeSeed199Weight p : ℝ) / 10 := by
  have h131 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 131 8 16 4 (49 / 10) = true from by
          decide +kernel)).2
  have h139 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 139 8 16 4 (50 / 10) = true from by
          decide +kernel)).2
  have h163 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 163 8 16 5 (51 / 10) = true from by
          decide +kernel)).2
  have h181 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 181 8 16 5 (52 / 10) = true from by
          decide +kernel)).2
  have h199 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 199 8 16 5 (53 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h131 h139 h163 h181 h199
  intro p hp
  have hprime : p.Prime ∧ p ≤ 199 := by exact primeSeed199_prime_supply p hp
  change
    p ∈
      [199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127] ++
        primeSeed113Primes at hp
  simp only [List.mem_append] at hp
  rcases hp with hnew | hold
  · by_cases h1 : p ≤ 113
    · have hn :
        ∀
          p ∈
            ([199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127] :
              List ℕ),
          113 < p := by
        decide +kernel
      exact False.elim ((Nat.not_lt_of_ge h1) (hn p hnew))
    · by_cases h2 : p ≤ 131
      · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h2)
        simp only [primeSeed199Weight, ite_eq_right h1, ite_eq_left h2, Nat.cast_ofNat]
        norm_num only [Nat.cast_ofNat] at hl
        linarith only [hl, h131]
      · by_cases h3 : p ≤ 139
        · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h3)
          simp only [primeSeed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
            Nat.cast_ofNat]
          norm_num only [Nat.cast_ofNat] at hl
          linarith only [hl, h139]
        · by_cases h4 : p ≤ 163
          · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h4)
            simp only [primeSeed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
              ite_eq_left h4, Nat.cast_ofNat]
            norm_num only [Nat.cast_ofNat] at hl
            linarith only [hl, h163]
          · by_cases h5 : p ≤ 181
            · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr h5)
              simp only [primeSeed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
                ite_eq_right h4, ite_eq_left h5, Nat.cast_ofNat]
              norm_num only [Nat.cast_ofNat] at hl
              linarith only [hl, h181]
            · have hl := Real.log_le_log (Nat.cast_pos.mpr hprime.1.pos) (Nat.cast_le.mpr hprime.2)
              simp only [primeSeed199Weight, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
                ite_eq_right h4, ite_eq_right h5, Nat.cast_ofNat]
              norm_num only [Nat.cast_ofNat] at hl
              linarith only [hl, h199]
  · have hp113 := (primeSeed113_prime_supply p hold).2
    simpa only [primeSeed199Weight, ite_eq_left hp113, primeSeed113Weight] using hprev p hold

end PseudoPrime.PrimeTestBounds.MillerRabin
