/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FourPoleCommonBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.CommonEndpointBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.OddMidscaleBounds

/-! # Common-scale fourth-pole bounds for Selfridge maxima

These consumers transfer the full-domain negative Jacobi candidate to all four stopping
maxima and to both classical trial maxima. The arithmetic exceptions are absorbed by
the entrance floor, and the totalized empty-domain trial count is preserved.
Numerical kernel certification remains in LLS and the Jacobi maximum in PseudoSquare.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- The common-scale fourth-pole floor exceeds the exceptional negative stopping cap.
Input: any natural endpoint. Claim: the candidate is at least twenty-seven.
Proof: compare the fixed entrance contribution with the candidate.
Role: transfer the Jacobi witness maximum without a low-input exception. -/
theorem fourPoleScale_ge_twenty_seven (B : ℕ) : 27 ≤ PseudoSquare.fourPoleScaleBound B :=
  (by norm_num only : (27 : ℝ) ≤ (777 / 1000 : ℝ) * ((10 : ℝ) ^ 18) ^ 2).trans
    (PseudoSquare.fourPole_scale_lower B)

/-- Under GRH all four stopping maxima obey the common-scale fourth-pole bound.
Input: any natural endpoint and GRH. Claim: both scans and both stopping semantics are covered.
Proof: apply the unconditional negative-witness transfer to the proved Jacobi maximum.
Role: expose the improved cumulative bound while preserving negative and factor-detecting stops. -/
theorem selfridgeMaxima_le_fourPole_scale (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleScaleBound B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleScaleBound B ∧
      (classicalNeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleScaleBound B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleScaleBound B :=
  selfridgeMaxima_le_of_QNegOne (fourPoleScale_ge_twenty_seven B)
    (PseudoSquare.QNegOne_le_fourPole_scale B hGRH)

/-- Both classical trial maxima obey the sharp transfer of the common-scale candidate.
Input: any natural endpoint and GRH. Claim: each count is at most the candidate minus three,
divided by two. Proof: use the unconditional totalized sharp count transfer.
Role: preserve empty-domain count one while removing the former loose additive trial allowance. -/
theorem classicalTrials_le_fourPole_scale (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ (PseudoSquare.fourPoleScaleBound B - 3) / 2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ (PseudoSquare.fourPoleScaleBound B - 3) / 2 :=
  ⟨classicalTrialCount_real_bound
      ((by norm_num only : (5 : ℝ) ≤ 27).trans (fourPoleScale_ge_twenty_seven B))
      (selfridgeMaxima_le_fourPole_scale B hGRH).1,
    classicalTrialCount_real_bound
      ((by norm_num only : (5 : ℝ) ≤ 27).trans (fourPoleScale_ge_twenty_seven B))
      (selfridgeMaxima_le_fourPole_scale B hGRH).2.2.1⟩

end PseudoPrime.PrimeTestBounds.Selfridge
