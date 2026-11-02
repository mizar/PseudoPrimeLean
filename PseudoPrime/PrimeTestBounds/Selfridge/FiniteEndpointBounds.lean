/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.CommonEndpointBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.OddMidscaleBounds
public import PseudoPrime.PseudoSquare.Bounds.FiniteEndpointBounds

/-! # Finite and refined endpoints for Selfridge stops

Negative and factor-detecting stops use distinct Jacobi cutoffs. The finite cap forty-seven
is never used for negative stops. Existing transfer theorems supply all four maxima and the
sharp classical trial estimate, including the convention at an empty admissible domain.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- The negative endpoint absorbs the exceptional stopping value twenty-seven. Input: an
endpoint at least three. Proof: each guarded candidate absorbs the exception. Role: expose
finite or refined endpoint bounds without new input enumeration. -/
theorem negOneEndpoint_ge_twentySeven {B : ℕ} (hB : 3 ≤ B) :
    27 ≤ PseudoSquare.negOneEndpointEnvelope B := by
  have hc := commonEnvelope_ge_twenty_seven hB
  apply le_min hc
  split_ifs
  · norm_num only
  · exact hc

/-- The non-one endpoint absorbs the exceptional stopping value fifteen. Input: an endpoint at
least three. Proof: each guarded candidate absorbs the exception. Role: expose finite or
refined endpoint bounds without new input enumeration. -/
theorem neOneEndpoint_ge_fifteen {B : ℕ} (hB : 3 ≤ B) :
    15 ≤ PseudoSquare.neOneEndpointEnvelope B := by
  have hc : (15 : ℝ) ≤ PseudoSquare.negOneEndpointEnvelope B :=
    (by norm_num only : (15 : ℝ) ≤ 27).trans (negOneEndpoint_ge_twentySeven hB)
  apply le_min hc
  split_ifs
  · norm_num only
  · exact hc

/-- All four stopping maxima obey their separate negative and non-one endpoints. Input: GRH
and an endpoint at least three. Proof: transfer the two witness maximum bounds. Role:
expose finite or refined endpoint bounds without new input enumeration. -/
theorem selfridgeMaxima_le_endpoints {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 3 ≤ B) :
    (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.negOneEndpointEnvelope B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ PseudoSquare.negOneEndpointEnvelope B ∧
      (classicalNeOneMaximum B : ℝ) ≤ PseudoSquare.neOneEndpointEnvelope B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ PseudoSquare.neOneEndpointEnvelope B := by
  have hn :=
    selfridgeMaxima_le_of_QNegOne (negOneEndpoint_ge_twentySeven hB)
      (PseudoSquare.QNegOne_le_endpoint hB hGRH)
  have he :=
    selfridgeNeOneMaxima_le_of_QNeOne_bound (neOneEndpoint_ge_fifteen hB)
      (PseudoSquare.QNeOne_le_endpoint hB hGRH)
  exact ⟨hn.1, hn.2.1, he.1, he.2⟩

/-- Both classical trial maxima obey their separate sharp endpoint-minus-three bounds. Input:
GRH and an endpoint at least three. Proof: apply the existing sharp real count theorem.
Role: expose finite or refined endpoint bounds without new input enumeration. -/
theorem classicalTrials_le_endpoints {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 3 ≤ B) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ (PseudoSquare.negOneEndpointEnvelope B - 3) / 2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ (PseudoSquare.neOneEndpointEnvelope B - 3) / 2 := by
  have h := selfridgeMaxima_le_endpoints hGRH hB
  exact
    ⟨classicalTrialCount_real_bound
        ((by norm_num only : (5 : ℝ) ≤ 27).trans (negOneEndpoint_ge_twentySeven hB)) h.1,
      classicalTrialCount_real_bound
        ((by norm_num only : (5 : ℝ) ≤ 15).trans (neOneEndpoint_ge_fifteen hB)) h.2.2.1⟩

/-- The common endpoint also yields the sharper classical trial bound. Input: GRH and an
endpoint at least three. Proof: use the sharp count theorem above five. Role: expose
finite or refined endpoint bounds without new input enumeration. -/
theorem classicalTrials_le_common_sharp {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 3 ≤ B) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ (PseudoSquare.commonEndpointEnvelope B - 3) / 2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ (PseudoSquare.commonEndpointEnvelope B - 3) / 2 := by
  have h := selfridgeMaxima_le_common_envelope hGRH hB
  have h5 : (5 : ℝ) ≤ PseudoSquare.commonEndpointEnvelope B :=
    (by norm_num only : (5 : ℝ) ≤ 27).trans (commonEnvelope_ge_twenty_seven hB)
  exact ⟨classicalTrialCount_real_bound h5 h.1, classicalTrialCount_real_bound h5 h.2.2.1⟩

/-- Below 750 all four stopping maxima are at most thirty-one without GRH. Input: an endpoint
below 750. Proof: transfer the existing negative finite certificate. Role: expose finite
or refined endpoint bounds without new input enumeration. -/
theorem selfridgeMaxima_le_thirtyOne {B : ℕ} (hB : B < 750) :
    classicalNegOneMaximum B ≤ 31 ∧
      wheel30NegOneMaximum B ≤ 31 ∧ classicalNeOneMaximum B ≤ 31 ∧ wheel30NeOneMaximum B ≤ 31 := by
  have h :=
    selfridgeMaxima_le_of_QNegOne (by norm_num only : (27 : ℝ) ≤ 31)
      (Nat.cast_le.mpr (PseudoSquare.QNegOne_le_thirty_one_of_lt_750 hB))
  exact ⟨Nat.cast_le.mp h.1, Nat.cast_le.mp h.2.1, Nat.cast_le.mp h.2.2.1, Nat.cast_le.mp h.2.2.2⟩

/-- Below one million both non-one stopping maxima are at most forty-seven without GRH. Input:
an endpoint below one million. Proof: transfer the existing non-one finite certificate.
Role: expose finite or refined endpoint bounds without new input enumeration. -/
theorem selfridgeNeOneMaxima_le_fortySeven {B : ℕ} (hB : B < 1000000) :
    classicalNeOneMaximum B ≤ 47 ∧ wheel30NeOneMaximum B ≤ 47 := by
  have h :=
    selfridgeNeOneMaxima_le_of_QNeOne_bound (by norm_num only : (15 : ℝ) ≤ 47)
      (Nat.cast_le.mpr (PseudoSquare.QNeOne_le_fortySeven hB))
  exact ⟨Nat.cast_le.mp h.1, Nat.cast_le.mp h.2⟩

end PseudoPrime.PrimeTestBounds.Selfridge
