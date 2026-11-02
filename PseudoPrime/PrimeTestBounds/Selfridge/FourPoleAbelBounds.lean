/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FourPoleAbelBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.CommonEndpointBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.OddMidscaleBounds

/-!
# Selfridge scans from the actual double-Abel fourth-pole entrances

The independent three-row quadratic candidate controls all stopping maxima and both
classical trial maxima. Its floor absorbs exceptional stops, and the generic transfers
retain totalized empty-domain trial counts. Selection against other public candidates
is left to a separate comparison module; this leaf has no Q5 selection dependency.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH, all four classical and Wheel30 stopping maxima obey the new K4 minimum.
Feed the full-domain negative Jacobi maximum and its floor 27 into the established
stopping transfer. This retains both stopping meanings without new scan assumptions. -/
theorem selfridgeMaxima_le_fourPole_abel (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleAbelBound B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleAbelBound B ∧
      (classicalNeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleAbelBound B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleAbelBound B := by
  exact
    selfridgeMaxima_le_of_QNegOne (PseudoSquare.fourPole_abel_ge_twenty_seven B)
      (PseudoSquare.QNegOne_le_fourPole_abel B hGRH)

/-- Under GRH, both classical trial maxima obey the sharp affine transfer of the new
K4 candidate. Its floor exceeds five, so the existing totalized count theorem applies
to both actual stopping maxima, including empty domains.
This carries the analytic entrance improvement through to actual classical trial costs. -/
theorem classicalTrials_le_fourPole_abel (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ (PseudoSquare.fourPoleAbelBound B - 3) / 2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ (PseudoSquare.fourPoleAbelBound B - 3) / 2 := by
  exact
    ⟨classicalTrialCount_real_bound
        ((by norm_num only : (5 : ℝ) ≤ 27).trans (PseudoSquare.fourPole_abel_ge_twenty_seven B))
        (selfridgeMaxima_le_fourPole_abel B hGRH).1,
      classicalTrialCount_real_bound
        ((by norm_num only : (5 : ℝ) ≤ 27).trans (PseudoSquare.fourPole_abel_ge_twenty_seven B))
        (selfridgeMaxima_le_fourPole_abel B hGRH).2.2.1⟩

end PseudoPrime.PrimeTestBounds.Selfridge
