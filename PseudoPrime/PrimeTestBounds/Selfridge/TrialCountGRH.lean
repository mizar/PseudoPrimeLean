/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTestBounds.Selfridge.TrialCount
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal

/-!
# GRH trial count bounds
-/

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH and `B ≥ 751`, the pure `-1` aggregate trial count is at most
`elementaryRadius B / 2 + 1`. Rewrite the stopping-value maximum as `QNegOne B` using
`classicalNegOneMaximum_eq_QNegOne_of_399_le`, apply `elementary_formula_real`, then apply
`classicalTrialCountThrough_real_le`. This is the real bound used by the explicit count theorem. -/
theorem classicalNegOneTrialMaximum_real_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ} (hB : 751 ≤ B) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ PseudoSquare.elementaryRadius B / 2 + 1 := by
  have hM : (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.elementaryRadius B := by
    have h399 : 399 ≤ B := by omega
    rw [classicalNegOneMaximum_eq_QNegOne_of_399_le h399]
    exact (PseudoSquare.elementary_formula_real hGRH (by omega)).2
  unfold classicalNegOneTrialMaximum
  have hbase := classicalTrialCountThrough_real_le (classicalNegOneMaximum B)
  linarith only [hbase, hM]

/-- Under GRH and `B ≥ 751`, the classical `≠1` aggregate trial count is at most the pure
`-1` aggregate count, and the latter is at most
`(log(4B) + (24/5)*loglog(4B) + 3)² / 2 + 1` as a real number.
Count monotonicity transports the stopping-value comparison; unfolding `elementaryRadius`
in `classicalNegOneTrialMaximum_real_le` gives the explicit upper bound. -/
theorem classicalTrialMaximum_elementary_bound_explicit
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ} (hB : 751 ≤ B) :
    classicalNeOneTrialMaximum B ≤ classicalNegOneTrialMaximum B ∧
      (classicalNegOneTrialMaximum B : ℝ) ≤
        (Real.log (4 * (B : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (B : ℝ))) + 3) ^ 2 / 2 +
          1 := by
  refine ⟨?_, ?_⟩
  · exact PrimeTest.classicalTrialCountThrough_mono
      (classicalNeOneMaximum_le_classicalNegOneMaximum B)
  · have := classicalNegOneTrialMaximum_real_le hGRH hB
    simpa only [PseudoSquare.elementaryRadius] using this

end PseudoPrime.PrimeTestBounds.Selfridge
