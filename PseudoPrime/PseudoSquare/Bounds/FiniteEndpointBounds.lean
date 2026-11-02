/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.CommonEndpointBounds
public import PseudoPrime.PseudoSquare.Computation.SmallN
public import PseudoPrime.PseudoSquare.Computation.MillionWitnessBridge

/-! # Guarded finite endpoints for quadratic witnesses

This consumer combines the refined elementary radius with completed finite bounds 31 and 47.
The latter applies only to non-one witnesses. Existing certificate leaves are reused unchanged;
new scalar guards do not enumerate number-theoretic inputs. Keep these selection rules outside
the finite certificate modules to limit revalidation after edits.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Intersect the negative common endpoint with the finite cap thirty-one below 750.
Input: any natural endpoint. Output: a real cutoff with its original finite guard.
Role: retain each certified negative-witness candidate without extrapolation. -/
noncomputable def negOneEndpointEnvelope (B : ℕ) : ℝ :=
  min (commonEndpointEnvelope B) (if B < 750 then 31 else commonEndpointEnvelope B)

/-- Intersect the negative endpoint with the non-one cap forty-seven below one million.
Input: any natural endpoint. Output: a real cutoff for non-one witnesses only.
Role: distinguish factor-detecting bounds from purely negative witnesses. -/
noncomputable def neOneEndpointEnvelope (B : ℕ) : ℝ :=
  min (negOneEndpointEnvelope B) (if B < 1000000 then 47 else negOneEndpointEnvelope B)

/-- The completed million-residue certificate bounds the non-one maximum by forty-seven.
Input: an endpoint below one million; no GRH is needed. Claim: the natural maximum is at most 47.
Proof: lift the existing pointwise certificate. Role: justify the non-one endpoint guard. -/
theorem QNeOne_le_fortySeven {B : ℕ} (hB : B < 1000000) : QNeOne B ≤ 47 := by
  have h : (QNeOne B : ℝ) ≤ 47 := by
    apply QNeOne_cast_le_of_forall (by norm_num only : (0 : ℝ) ≤ 47)
    intro n hn
    have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
    exact
      Nat.cast_le.mpr
        (primeNeOneWitness_le_fortySeven_of_lt_million ha.odd ha.not_isSquare (ha.le.trans_lt hB))
  exact Nat.cast_le.mp h

/-- The guarded negative endpoint bounds its cumulative witness maximum.
Input: GRH and an endpoint at least three. Claim: the negative maximum fits the endpoint.
Proof: intersect the common and applicable finite bounds. Role: supply the public cutoff. -/
theorem QNegOne_le_endpoint {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ negOneEndpointEnvelope B := by
  have hc := (witnessMaxima_le_common_envelope hGRH hB).1
  apply le_min hc
  split_ifs with h
  · exact Nat.cast_le.mpr (QNegOne_le_thirty_one_of_lt_750 h)
  · exact hc

/-- The guarded non-one endpoint bounds its cumulative witness maximum.
Input: GRH and an endpoint at least three. Claim: the non-one maximum fits the endpoint.
Proof: use witness inclusion and the finite cap. Role: supply the factor-detecting cutoff. -/
theorem QNeOne_le_endpoint {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNeOne B : ℝ) ≤ neOneEndpointEnvelope B := by
  have hc := (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans (QNegOne_le_endpoint hB hGRH)
  apply le_min hc
  split_ifs with h
  · exact Nat.cast_le.mpr (QNeOne_le_fortySeven h)
  · exact hc

/-- The negative endpoint never exceeds the preceding common endpoint.
Input: any natural endpoint. Proof: the left minimum inequality. Role: retain prior bounds. -/
theorem negOneEndpoint_le_common (B : ℕ) : negOneEndpointEnvelope B ≤ commonEndpointEnvelope B :=
  min_le_left _ _

/-- The non-one endpoint never exceeds the negative endpoint.
Input: any natural endpoint. Proof: the left minimum inequality. Role: retain witness inclusion. -/
theorem neOneEndpoint_le_negative (B : ℕ) : neOneEndpointEnvelope B ≤ negOneEndpointEnvelope B :=
  min_le_left _ _

/-- The thirty-one cap is retained on its certified side of 750.
Input: an endpoint below 750. Claim: the negative endpoint is at most 31.
Proof: select the guarded minimum branch. Role: expose the finite improvement. -/
theorem negOneEndpoint_le_thirtyOne {B : ℕ} (hB : B < 750) : negOneEndpointEnvelope B ≤ 31 :=
  (min_le_right _ _).trans_eq (ite_eq_left hB)

/-- The forty-seven cap is retained exactly below one million.
Input: the strict endpoint upper bound. Claim: the non-one endpoint is at most 47.
Proof: select the guarded minimum branch. Role: expose the factor-detecting finite improvement. -/
theorem neOneEndpoint_le_fortySeven {B : ℕ} (hB : B < 1000000) : neOneEndpointEnvelope B ≤ 47 :=
  (min_le_right _ _).trans_eq (ite_eq_left hB)

/-- The refined common endpoint never exceeds its original additive-three formula.
Input: an endpoint at least three. Claim: comparison with the complete previous minimum.
Proof: lower only the elementary term. Role: compare published selections, not isolated radii. -/
theorem commonEnvelope_le_previous {B : ℕ} (hB : 3 ≤ B) :
    commonEndpointEnvelope B ≤
      min (elementaryRadius B)
        (min (jointEndpointBound B)
          (if Real.log B ≤ 1609 / 25 then 4093 else jointEndpointBound B)) :=
  min_le_min (refinedRadius_lt_elementary hB).le (le_refl _)

end PseudoPrime.PseudoSquare
