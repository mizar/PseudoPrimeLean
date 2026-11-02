/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FourPoleReducedBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.CommonEndpointBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.OddMidscaleBounds

/-! # Reduced fourth-pole entrances for Selfridge scans

The minimum of the three certified rows controls all four stopping maxima and both
classical trial maxima. The entrance floor absorbs exceptional stopping values and
preserves the totalized trial count on empty domains. Kernel certification remains in
LLS, while the cumulative Jacobi candidate belongs to PseudoSquare.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- All four Selfridge stopping maxima obey the reduced fourth-pole minimum under GRH.
Input: any natural endpoint and GRH. Claim: both scans and stopping semantics are covered.
Proof: transfer the full-domain negative maximum and its exceptional-value floor.
Role: connect all three reduced entrances to the public Selfridge maxima. -/
theorem selfridgeMaxima_le_fourPole_reduced (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleReducedBound B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleReducedBound B ∧
      (classicalNeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleReducedBound B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleReducedBound B :=
  selfridgeMaxima_le_of_QNegOne (PseudoSquare.fourPole_reduced_ge_twenty_seven B)
    (PseudoSquare.QNegOne_le_fourPole_reduced B hGRH)

/-- Both classical trial maxima obey the sharp transfer of the reduced minimum.
Input: any natural endpoint and GRH. Claim: each count is at most the bound minus three,
divided by two. Proof: apply the totalized sharp classical count comparison.
Role: carry the finite-entrance improvement through to actual trial costs. -/
theorem classicalTrials_le_fourPole_reduced (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ (PseudoSquare.fourPoleReducedBound B - 3) / 2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ (PseudoSquare.fourPoleReducedBound B - 3) / 2 :=
  ⟨classicalTrialCount_real_bound
      ((by norm_num only : (5 : ℝ) ≤ 27).trans (PseudoSquare.fourPole_reduced_ge_twenty_seven B))
      (selfridgeMaxima_le_fourPole_reduced B hGRH).1,
    classicalTrialCount_real_bound
      ((by norm_num only : (5 : ℝ) ≤ 27).trans (PseudoSquare.fourPole_reduced_ge_twenty_seven B))
      (selfridgeMaxima_le_fourPole_reduced B hGRH).2.2.1⟩

end PseudoPrime.PrimeTestBounds.Selfridge
