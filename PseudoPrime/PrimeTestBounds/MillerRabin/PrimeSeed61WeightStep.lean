/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Checks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Checks

/-! # Logarithmic weight extension through 61 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the logarithmic bound for the previous supply, extend it to the labels through 61.
The proof checks the new cutoffs and uses the hypothesis for earlier labels. -/
theorem primeSeed61_weight_step
    (hprev : ∀ p ∈ primeSeed43Primes, Real.log p ≤ (primeSeed43Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed61Primes, Real.log p ≤ (primeSeed61Weight p : ℝ) / 10 := by
  have h47 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 47 6 16 3 (39 / 10) = true from by
          decide +kernel)).2
  have h53 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 53 6 16 3 (40 / 10) = true from by
          decide +kernel)).2
  have h59 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 59 6 16 4 (41 / 10) = true from by
          decide +kernel)).2
  have h61 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 61 6 16 4 (42 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h47 h53 h59 h61
  intro p hp
  change p ∈ primeSeed43Primes ++ [47, 53, 59, 61] at hp
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | rfl | rfl | rfl | rfl
  · have hp43 := (primeSeed43_prime_supply p hp).2
    simpa only [primeSeed61Weight, ite_eq_left hp43, primeSeed43Weight] using hprev p hp
  · norm_num only [primeSeed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h47
  · norm_num only [primeSeed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h53
  · norm_num only [primeSeed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h59
  · norm_num only [primeSeed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h61

end PseudoPrime.PrimeTestBounds.MillerRabin
