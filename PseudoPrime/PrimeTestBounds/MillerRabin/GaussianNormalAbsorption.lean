/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLowFloorOrder
public import PseudoPrime.Analysis.GaussianSeededSharpComparison

/-! # Absorbing current analytic candidates in the normal plotting range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Up to scale 240 the fine seeded selection is still its 35000 floor.
Its first exact switch lies strictly above 240. -/
theorem seededSharp_le35000_240 {L : ℝ} (hU : L ≤ 240) :
    Analysis.gaussianSeededSharp L ≤ (35000 : ℝ) := by
  have h35 : L ≤ Analysis.gaussianSeededSharpSwitch false 35000 :=
    hU.trans Analysis.gaussianSeededSharp_switch35_bounds.1.le
  simp only [Analysis.gaussianSeededSharp, Analysis.gaussianSeededSharpSelected, ite_eq_left h35,
    le_refl]

/-- Above scale 100 and below the first new high guard, the minimum of the
fine Gaussian and seeded candidates is at most the old baseline selection.
Resolve its four successive analytic regions, including the short fixed-floor region. -/
theorem gaussianSeeded_min_le_next {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n < 30000000000) :
    min (Analysis.gaussianLowFamily (Real.log n)) (Analysis.gaussianSeededSharp (Real.log n)) ≤
      nextWitnessEnvelope n := by
  let A := min (Analysis.gaussianLowFamily (Real.log n)) (Analysis.gaussianSeededSharp (Real.log n))
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hG : A ≤ Analysis.gaussian1000Bound (Real.log n) :=
    (min_le_left _ _).trans
      ((gaussianLowFamily_lt_recovered (by linarith only [hL] : (0 : ℝ) ≤ Real.log n)).le.trans
        (Analysis.gaussianRecovered_bound_le _))
  have hP : A ≤ LLS.PaperStatements.pointwiseCutoff (Real.log n) :=
    (min_le_left _ _).trans (gaussianLowFamily_lt_pointwise hL).le
  by_cases h132 : Real.log n < 132
  · rw [next_eq_middle_three hn hL h132]
    exact le_min hP (le_min ((min_le_left _ _).trans (gaussianLowFamily_lt_reflected hL).le) hG)
  · by_cases h235 : Real.log n ≤ 235
    · rw [next_eq_middle_two hn (le_of_not_gt h132) h235]
      exact le_min hP hG
    · by_cases h240 : Real.log n < 240
      · rw [next_eq_fixed_gaussian hn (lt_of_not_ge h235) h240]
        exact le_min ((min_le_right _ _).trans (seededSharp_le35000_240 h240.le)) hG
      · rw [next_eq_seeded hn (le_of_not_gt h240) (by linarith only [hU])]
        exact
          (min_le_right _ _).trans
            ((Analysis.gaussianSeededSharp_le_seeded h63).trans
              (Analysis.gaussianRecoveredSeeded_le_seeded h63))

/-- In the analytic normal range, the current refined envelope is redundant
beside the fine Gaussian and seeded candidates. Compare every active current
candidate and exclude both old high guards with the explicit logarithmic upper bound. -/
theorem min_refined_gaussianSeeded_eq {n : ℕ} (hn : 1 < n) (hL : 100 ≤ Real.log n)
    (hU : Real.log n < 30000000000) :
    min (refinedSelectedEnvelope n)
        (min (Analysis.gaussianLowFamily (Real.log n))
          (Analysis.gaussianSeededSharp (Real.log n))) =
      min (Analysis.gaussianLowFamily (Real.log n))
        (Analysis.gaussianSeededSharp (Real.log n)) := by
  let A := min (Analysis.gaussianLowFamily (Real.log n)) (Analysis.gaussianSeededSharp (Real.log n))
  have h63 : (63 : ℝ) ≤ Real.log n := by linarith only [hL]
  apply min_eq_right
  rw [← refined_eq_selected hn]
  apply refined_lower_of_candidates
  · rw [lowPrimeTight_eq_next_of_log (by linarith only [hL])]
    exact gaussianSeeded_min_le_next hn hL hU
  · intro _
    exact
      (min_le_left _ _).trans
        (gaussianLowFamily_lt_recovered (by linarith only [hL] : (0 : ℝ) ≤ Real.log n)).le
  · intro _
    exact (min_le_left _ _).trans (gaussianLowFamily_lt_gamma hL).le
  · intro _
    exact (min_le_right _ _).trans (Analysis.gaussianSeededSharp_le_seeded h63)
  · intro hh
    exfalso
    linarith only [hU, hh]
  · intro hh
    exfalso
    linarith only [hU, hh]

end PseudoPrime.PrimeTestBounds.MillerRabin
