/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltClassification
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Lower logarithmic scale for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A uniform Korselt triple is at least 8911. Below `2^22` this follows from
the complete finite classification; larger inputs exceed the bound directly. -/
theorem uniformKorselt_ge_8911 {n : ℕ} (hu : UniformKorseltTriple n) : 8911 ≤ n := by
  by_cases h : n ≤ 2 ^ 22
  · have hc := uniformKorselt_le_pow22_cases hu h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h
    all_goals subst n; norm_num only
  · have hn : 2 ^ 22 < n := Nat.lt_of_not_ge h
    exact le_trans (by norm_num only : 8911 ≤ 2 ^ 22) (Nat.le_of_lt hn)

/-- Every uniform Korselt triple has logarithm at least eight. The finite
classification gives a lower bound exceeding 3000, and a rational logarithmic
certificate transfers this to the real logarithm. -/
theorem uniformKorselt_log_ge_eight {n : ℕ} (hu : UniformKorseltTriple n) :
    (8 : ℝ) ≤ Real.log n := by
  have hn : 3000 ≤ n := le_trans (by norm_num only) (uniformKorselt_ge_8911 hu)
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3000 12 12 8 (801 / 100) = true by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog
  exact hlog.trans (Real.log_le_log (by norm_num only) (Nat.cast_le.mpr hn))

end PseudoPrime.PrimeTestBounds.MillerRabin
