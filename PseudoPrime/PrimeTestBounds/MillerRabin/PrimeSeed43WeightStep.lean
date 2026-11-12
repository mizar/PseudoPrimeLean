/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Checks
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithmic weight extension through 43 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given the logarithmic bound for the previous supply, extend it to the labels through 43.
The proof checks the new cutoffs and uses the hypothesis for earlier labels. -/
theorem primeSeed43_weight_step
    (hprev : ∀ p ∈ primeSeed19Primes, Real.log p ≤ (primeSeed19Weight p : ℝ) / 10) :
    ∀ p ∈ primeSeed43Primes, Real.log p ≤ (primeSeed43Weight p : ℝ) / 10 := by
  have h23 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 23 5 16 3 (32 / 10) = true from by
          decide +kernel)).2
  have h31 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 31 5 16 3 (35 / 10) = true from by
          decide +kernel)).2
  have h43 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 43 6 16 3 (38 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h23 h31 h43
  have h29 : Real.log (29 : ℝ) ≤ (7 / 2 : ℝ) :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (29 : ℝ) ≤ 31)).trans h31
  have h37 : Real.log (37 : ℝ) ≤ (19 / 5 : ℝ) :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (37 : ℝ) ≤ 43)).trans h43
  have h41 : Real.log (41 : ℝ) ≤ (19 / 5 : ℝ) :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (41 : ℝ) ≤ 43)).trans h43
  intro p hp
  simp only [primeSeed43Primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num only [primeSeed43Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
  · have h := hprev 2 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · have h := hprev 3 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · have h := hprev 5 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · have h := hprev 7 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · have h := hprev 11 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · have h := hprev 13 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · have h := hprev 17 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · have h := hprev 19 (by decide)
    norm_num only [primeSeed19Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false] at h
    exact h
  · exact h23
  · exact h29
  · exact h31
  · exact h37
  · exact h41
  · exact h43

end PseudoPrime.PrimeTestBounds.MillerRabin
