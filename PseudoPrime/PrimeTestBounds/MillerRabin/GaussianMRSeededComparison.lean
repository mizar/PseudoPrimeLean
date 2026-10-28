/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRSeededComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMRSeededWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.ImprovedIntervalSelection

/-! # Effective comparisons for seeded Gaussian witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Below the triangular threshold, the two strict Gaussian ranges improve the
previous all-input witness envelope. The shared 50000 plateau is excluded. -/
theorem gaussianSeeded_lt_improved {n : ℕ} (hn : 1 < n) (hU : Real.log n < 2000000000000)
    (hstrict :
      (Analysis.gaussianFloorSwitch false 35000 < Real.log n ∧
          Real.log n < Analysis.gaussianSeededSwitch false 50000) ∨
        Analysis.gaussianFloorSwitch true 50000 < Real.log n) :
    Analysis.gaussianSeededSelected (Real.log n) < improvedWitnessEnvelope n := by
  have h240 : (240 : ℝ) < Real.log n := by
    rcases hstrict with h | h
    · linarith only [h.1, Analysis.gaussianFloor_switch35_bounds.1]
    · linarith only [h, (Analysis.gaussianFloor_switch50_bounds true).1]
  rw [improved_eq_gaussian hn h240 hU]
  rcases hstrict with h | h
  · exact Analysis.gaussianSeeded_strict_first h.1 h.2
  · exact Analysis.gaussianSeeded_strict_last h

end PseudoPrime.PrimeTestBounds.MillerRabin
