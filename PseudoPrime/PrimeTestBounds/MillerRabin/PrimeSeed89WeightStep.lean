/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Checks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Checks

/-! # Logarithmic weight extension through 89 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the logarithmic bound for the previous supply, extend it to the labels through 89.
The proof checks the new cutoffs and uses the hypothesis for earlier labels. -/
theorem primeSeed89_weight_step
    (hprev : ∀ p ∈ primeSeed61Primes, Real.log p ≤ (primeSeed61Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed89Primes, Real.log p ≤ (primeSeed89Weight p : ℝ) / 10 := by
  have h73 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 73 7 16 4 (43 / 10) = true from by
          decide +kernel)).2
  have h79 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 79 7 16 4 (44 / 10) = true from by
          decide +kernel)).2
  have h89 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 89 7 16 4 (45 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h73 h79 h89
  have h67 : Real.log (67 : ℝ) ≤ 43 / 10 :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (67 : ℝ) ≤ 73)).trans h73
  have h71 : Real.log (71 : ℝ) ≤ 43 / 10 :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (71 : ℝ) ≤ 73)).trans h73
  have h83 : Real.log (83 : ℝ) ≤ 9 / 2 :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (83 : ℝ) ≤ 89)).trans h89
  intro p hp
  change p ∈ primeSeed61Primes ++ [67, 71, 73, 79, 83, 89] at hp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl
  · have hp61 := (primeSeed61_prime_supply p hp).2
    simpa only [primeSeed89Weight, ite_eq_left hp61, primeSeed61Weight] using hprev p hp
  all_goals norm_num only [primeSeed89Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
  all_goals
    first
    | exact h67
    | exact h71
    | exact h73
    | exact h79
    | exact h83
    | exact h89

end PseudoPrime.PrimeTestBounds.MillerRabin
