/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Checks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Checks

/-! # Logarithmic weight extension through 113 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the logarithmic bound for the previous supply, extend it to the labels through 113.
The proof checks the new cutoffs and uses the hypothesis for earlier labels. -/
theorem primeSeed113_weight_step
    (hprev : ∀ p ∈ primeSeed89Primes, Real.log p ≤ (primeSeed89Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed113Primes, Real.log p ≤ (primeSeed113Weight p : ℝ) / 10 := by
  have h97 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 97 7 16 4 (46 / 10) = true from by
          decide +kernel)).2
  have h109 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 109 7 16 4 (47 / 10) = true from by
          decide +kernel)).2
  have h113 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 113 7 16 4 (48 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h97 h109 h113
  have h101 : Real.log (101 : ℝ) ≤ 47 / 10 :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (101 : ℝ) ≤ 109)).trans h109
  have h103 : Real.log (103 : ℝ) ≤ 47 / 10 :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (103 : ℝ) ≤ 109)).trans h109
  have h107 : Real.log (107 : ℝ) ≤ 47 / 10 :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (107 : ℝ) ≤ 109)).trans h109
  intro p hp
  change p ∈ [113, 109, 107, 103, 101, 97] ++ primeSeed89Primes at hp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) | hp
  all_goals
    try norm_num only [primeSeed113Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
  all_goals
    first
    | exact h113
    | exact h109
    | exact h107
    | exact h103
    | exact h101
    | exact h97
    | ( have hp89 := (primeSeed89_prime_supply p hp).2
        simpa only [primeSeed113Weight, ite_eq_left hp89, primeSeed89Weight] using hprev p hp)

end PseudoPrime.PrimeTestBounds.MillerRabin
