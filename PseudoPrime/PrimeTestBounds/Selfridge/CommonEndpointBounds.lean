/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.TrialCountGRH
public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer
public import PseudoPrime.PseudoSquare.Bounds.CommonEndpointBounds

/-! # Common-endpoint bounds for Selfridge maxima and trial counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- A real QNegOne bound X>=27 bounds the classical negative maximum. Transfer the
unconditional max(27,QNegOne) comparison after casting. The empty maximum is included,
and later analytic bounds need no new first-stop argument. -/
theorem classicalMaximum_le_of_QNegOne {B : ℕ} {X : ℝ} (h27 : 27 ≤ X)
    (hQ : (PseudoSquare.QNegOne B : ℝ) ≤ X) : (classicalNegOneMaximum B : ℝ) ≤ X := by
  have hm : (classicalNegOneMaximum B : ℝ) ≤ (max 27 (PseudoSquare.QNegOne B) : ℕ) :=
    Nat.cast_le.mpr (classicalNegOneMaximum_le_max_27_QNegOne B)
  rw [Nat.cast_max, Nat.cast_ofNat] at hm
  exact hm.trans (max_le h27 hQ)

/-- A QNegOne bound X>=27 bounds all four classical and Wheel30 stopping maxima.
Use the negative maximum transfer, equality of both scans and inclusion of non-one
stops. No analytic or GRH assumption is added by this generic consumer. -/
theorem selfridgeMaxima_le_of_QNegOne {B : ℕ} {X : ℝ} (h27 : 27 ≤ X)
    (hQ : (PseudoSquare.QNegOne B : ℝ) ≤ X) :
    (classicalNegOneMaximum B : ℝ) ≤ X ∧
      (wheel30NegOneMaximum B : ℝ) ≤ X ∧
      (classicalNeOneMaximum B : ℝ) ≤ X ∧ (wheel30NeOneMaximum B : ℝ) ≤ X := by
  have hc := classicalMaximum_le_of_QNegOne h27 hQ
  have hn := (Nat.cast_le.mpr (classicalNeOneMaximum_le_classicalNegOneMaximum B)).trans hc
  exact
    ⟨hc, (wheel30NegOneMaximum_eq_classicalNegOneMaximum B) ▸ hc, hn,
      (wheel30NeOneMaximum_eq_classicalNeOneMaximum B) ▸ hn⟩

/-- For B>=3, the combined envelope absorbs the exceptional negative stopping value 27.
The elementary radius exceeds 31 and both endpoint candidates exceed 27. This permits
Selfridge transfer without modifying the envelope by an additional maximum. -/
theorem commonEnvelope_ge_twenty_seven {B : ℕ} (hB : 3 ≤ B) :
    27 ≤ PseudoSquare.commonEndpointEnvelope B := by
  have he : (27 : ℝ) ≤ PseudoSquare.elementaryRadius B :=
    (by norm_num only : (27 : ℝ) ≤ 31).trans (PseudoSquare.thirtyOne_lt_elementaryRadius hB).le
  have hj : (27 : ℝ) ≤ PseudoSquare.jointEndpointBound B := by
    have hm := le_max_left (255 : ℝ) (Real.log B)
    unfold PseudoSquare.jointEndpointBound
    nlinarith only [hm, sq_nonneg (max 255 (Real.log B) - 255)]
  unfold PseudoSquare.commonEndpointEnvelope
  apply le_min he (le_min hj ?_)
  split_ifs
  · norm_num only
  · exact hj

/-- Under GRH and B>=3, all four stopping maxima obey the combined common-endpoint
bound. Feed the proved QNegOne envelope into the generic maximum transfer and absorb
27. This covers every admissible input through B for either stopping rule. -/
theorem selfridgeMaxima_le_common_envelope {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 3 ≤ B) :
    (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.commonEndpointEnvelope B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ PseudoSquare.commonEndpointEnvelope B ∧
      (classicalNeOneMaximum B : ℝ) ≤ PseudoSquare.commonEndpointEnvelope B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ PseudoSquare.commonEndpointEnvelope B := by
  exact
    selfridgeMaxima_le_of_QNegOne (commonEnvelope_ge_twenty_seven hB)
      (PseudoSquare.witnessMaxima_le_common_envelope hGRH hB).1

/-- Under GRH and log B<=1609/25, all stopping maxima are at most 4093, including empty
input domains. Apply the full low-domain QNegOne bound and absorb 27. The result is
natural-valued and feeds the exact classical trial-count bound. -/
theorem selfridgeMaxima_le_fixed_cap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlog : Real.log B ≤ 1609 / 25) :
    classicalNegOneMaximum B ≤ 4093 ∧
      wheel30NegOneMaximum B ≤ 4093 ∧
      classicalNeOneMaximum B ≤ 4093 ∧ wheel30NeOneMaximum B ≤ 4093 := by
  have h :=
    selfridgeMaxima_le_of_QNegOne (by norm_num only : (27 : ℝ) ≤ (4093 : ℕ))
      (Nat.cast_le.mpr (PseudoSquare.witnessMaxima_le_fixed_cap hGRH hlog).1)
  exact ⟨Nat.cast_le.mp h.1, Nat.cast_le.mp h.2.1, Nat.cast_le.mp h.2.2.1, Nat.cast_le.mp h.2.2.2⟩

/-- Under GRH and log B<=1609/25, both classical trial maxima are at most 2045.
Transport stopping maxima <=4093 through count monotonicity and compute the single
scalar count. On an empty domain the conventional count one also satisfies the bound. -/
theorem classicalTrials_le_fixed_cap {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlog : Real.log B ≤ 1609 / 25) :
    classicalNegOneTrialMaximum B ≤ 2045 ∧ classicalNeOneTrialMaximum B ≤ 2045 := by
  have h := selfridgeMaxima_le_fixed_cap hGRH hlog
  have hc : PrimeTest.classicalTrialCountThrough 4093 = 2045 := by decide
  exact
    ⟨(PrimeTest.classicalTrialCountThrough_mono h.1).trans hc.le,
      (PrimeTest.classicalTrialCountThrough_mono h.2.2.1).trans hc.le⟩

/-- Under GRH and B>=3, both classical real trial maxima obey envelope/2+1.
Combine the stopping bounds with the unconditional real count inequality. This is a
uniform trial estimate without enumerating candidate stops or input integers. -/
theorem classicalTrials_le_common_envelope {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hB : 3 ≤ B) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ PseudoSquare.commonEndpointEnvelope B / 2 + 1 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ PseudoSquare.commonEndpointEnvelope B / 2 + 1 := by
  have h := selfridgeMaxima_le_common_envelope hGRH hB
  have hn := classicalTrialCountThrough_real_le (classicalNegOneMaximum B)
  have he := classicalTrialCountThrough_real_le (classicalNeOneMaximum B)
  constructor
  · exact hn.trans (by linarith only [h.1])
  · exact he.trans (by linarith only [h.2.2.1])

end PseudoPrime.PrimeTestBounds.Selfridge
