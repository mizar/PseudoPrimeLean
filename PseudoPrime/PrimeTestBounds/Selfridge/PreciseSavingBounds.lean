/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.PreciseSavingCumulative
public import PseudoPrime.PseudoSquare.Bounds.PreciseSavingEnvelope
public import PseudoPrime.PrimeTestBounds.Selfridge.CommonEndpointBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.OddMidscaleBounds

/-! # Precise-saving radii for Selfridge stopping values and classical trials

Negative Jacobi radii bound both stopping semantics and both scans. On nonempty input
ranges their floors absorb the exceptional stopping values. Empty stopping maxima stay
zero and the totalized classical trial count stays one, so all-domain trial bounds retain
an explicit maximum with one rather than apply the sharp subtraction formula unguarded.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Below endpoint three the admissible input finset is empty.
Input: that endpoint condition. Claim: no odd nonsquare lies in the finite domain.
Proof: otherwise its positive prime witness would lie below the zero Jacobi maximum.
Role: preserve exact stopping and totalized trial boundary values. -/
private theorem precise_empty_inputs {B : ℕ} (hB : B < 3) :
    NumberTheory.admissibleFinset B = ∅ := by
  classical
  have hz := (PseudoSquare.witnessMaxima_eq_zero_of_small hB).1
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have ha := NumberTheory.mem_admissibleFinset_iff.mp hn
  have hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare ha.odd ha.not_isSquare
  have hp := (NumberTheory.primeNegOneWitness_mem n hw).1.pos
  have hle := PseudoSquare.primeNegOneWitness_le_QNegOne hn
  rw [hz] at hle
  exact (Nat.not_le_of_lt hp) hle

/-- All four empty stopping maxima are zero and both classical trial maxima are one.
Input: an endpoint below three. Claim: the original empty-domain conventions are unchanged.
Proof: unfold the supremum over the empty input set, then evaluate the totalized count.
Role: prevent an invalid unguarded subtraction of three from a small real radius. -/
theorem precise_empty_boundary {B : ℕ} (hB : B < 3) :
    classicalNegOneMaximum B = 0 ∧
      wheel30NegOneMaximum B = 0 ∧
      classicalNeOneMaximum B = 0 ∧
      wheel30NeOneMaximum B = 0 ∧
      classicalNegOneTrialMaximum B = 1 ∧ classicalNeOneTrialMaximum B = 1 := by
  classical
  have he := precise_empty_inputs hB
  have hc : classicalNegOneMaximum B = 0 := by
    dsimp only [classicalNegOneMaximum]
    apply (Finset.sup_eq_bot_iff _ _).mpr
    intro n _
    exact False.elim ((Finset.eq_empty_iff_forall_notMem.mp he) n.val n.property)
  have hn : classicalNeOneMaximum B = 0 := by
    dsimp only [classicalNeOneMaximum]
    apply (Finset.sup_eq_bot_iff _ _).mpr
    intro n _
    exact False.elim ((Finset.eq_empty_iff_forall_notMem.mp he) n.val n.property)
  exact
    ⟨hc, (wheel30NegOneMaximum_eq_classicalNegOneMaximum B).trans hc, hn,
      (wheel30NeOneMaximum_eq_classicalNeOneMaximum B).trans hn, by
      rw [classicalNegOneTrialMaximum, hc]; rfl, by
      rw [classicalNeOneTrialMaximum, hn]; rfl⟩

/-- On nonempty input ranges, both precise-saving radii cover all four stopping maxima.
Input: an endpoint at least three and GRH. Claim: the smaller radius bounds both scan semantics.
Proof: absorb the exceptional cap twenty-seven and transfer the negative Jacobi maximum.
Role: Selfridge consumers of both Ra and R31 without changing factor-detecting stops. -/
theorem selfridgeMaxima_le_preciseRadii {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) ∧
      (wheel30NegOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) ∧
      (classicalNeOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) ∧
      (wheel30NeOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) := by
  have h27 :=
    le_min
      ((by norm_num only : (27 : ℝ) ≤ 31).trans (PseudoSquare.preciseRadius_gt_thirty_one hB).le)
      ((by norm_num only : (27 : ℝ) ≤ 81).trans (PseudoSquare.prime31Radius_gt_eighty_one hB).le)
  exact selfridgeMaxima_le_of_QNegOne h27 (PseudoSquare.witnessMaxima_le_preciseRadii B hGRH).1

/-- Both precise-saving radii bound all four stopping maxima at every natural endpoint.
Input: any endpoint and GRH. Claim: the smaller radius is valid even on an empty domain.
Proof: use the nonempty-domain transfer or the exact zero stopping values.
Role: an all-domain stopping interface preserving the original boundary convention. -/
theorem selfridgeMaxima_le_preciseAll (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) ∧
      (wheel30NegOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) ∧
      (classicalNeOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) ∧
      (wheel30NeOneMaximum B : ℝ) ≤
        min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) := by
  by_cases hB : 3 ≤ B
  · exact selfridgeMaxima_le_preciseRadii hB hGRH
  · have he := precise_empty_boundary (Nat.lt_of_not_ge hB)
    simp only [he.1, he.2.1, he.2.2.1, he.2.2.2.1, Nat.cast_zero]
    have h0 :
      (0 : ℝ) ≤ min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) :=
      le_min (sq_nonneg _) (sq_nonneg _)
    exact ⟨h0, h0, h0, h0⟩

/-- Both classical trial maxima obey the sharp precise-radius transfer from endpoint three.
Input: an endpoint at least three and GRH. Claim: each count is at most (U-3)/2.
Proof: use the positive entrance floors with the established sharp count transfer.
Role: retain the improvement of the stopping radius in actual classical trial costs. -/
theorem classicalTrials_le_preciseRadii {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤
        (min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) - 3) /
          2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤
        (min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) - 3) /
          2 := by
  have h5 :=
    le_min
      ((by norm_num only : (5 : ℝ) ≤ 31).trans (PseudoSquare.preciseRadius_gt_thirty_one hB).le)
      ((by norm_num only : (5 : ℝ) ≤ 81).trans (PseudoSquare.prime31Radius_gt_eighty_one hB).le)
  have hm := selfridgeMaxima_le_preciseRadii hB hGRH
  exact ⟨classicalTrialCount_real_bound h5 hm.1, classicalTrialCount_real_bound h5 hm.2.2.1⟩

/-- Every real stopping bound yields a sharp totalized trial bound with an explicit floor one.
Input: a natural stopping value bounded by a real number. Claim: the count fits max(1,(X-3)/2).
Proof: separate stopping values below five from the established sharp count branch.
Role: preserve count one without requiring an artificial lower radius at empty endpoints. -/
theorem classicalTrialCount_real_max {i : ℕ} {X : ℝ} (hi : (i : ℝ) ≤ X) :
    (PrimeTest.classicalTrialCountThrough i : ℝ) ≤ max 1 ((X - 3) / 2) := by
  by_cases h5 : 5 ≤ i
  · exact
      (classicalTrialCountThrough_real_le_sub_three h5).trans
        ((div_le_div_of_nonneg_right (sub_le_sub_right hi 3) (by norm_num only : (0 : ℝ) ≤ 2)).trans
          (le_max_right _ _))
  · rw [PrimeTest.classicalTrialCountThrough, Nat.sub_eq_zero_of_le (Nat.lt_of_not_ge h5).le]
    norm_num only
    exact le_max_left _ _

/-- Both classical trial maxima satisfy the precise-radius bound at every natural endpoint.
Input: any endpoint and GRH. Claim: the explicit maximum with one covers empty domains.
Proof: apply the totalized transfer to the all-domain stopping bounds.
Role: the full-domain trial interface for Ra and R31. -/
theorem classicalTrials_le_preciseAll (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤
        max 1
          ((min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) - 3) /
            2) ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤
        max 1
          ((min (PseudoSquare.preciseElementaryRadius B) (PseudoSquare.prime31SavingRadius B) - 3) /
            2) := by
  have hm := selfridgeMaxima_le_preciseAll B hGRH
  exact ⟨classicalTrialCount_real_max hm.1, classicalTrialCount_real_max hm.2.2.1⟩

/-- The full new negative envelope bounds all four stopping maxima at every endpoint.
Input: any natural endpoint and GRH. Claim: the complete old minimum and both new radii
are retained for both scans and stopping semantics. Proof: transfer the nonempty floor;
on the empty domain use the exact zero maxima.
Role: the complete precise-saving Selfridge stopping interface. -/
theorem selfridgeMaxima_le_preciseSaving (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.preciseSavingEnvelope B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ PseudoSquare.preciseSavingEnvelope B ∧
      (classicalNeOneMaximum B : ℝ) ≤ PseudoSquare.preciseSavingEnvelope B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ PseudoSquare.preciseSavingEnvelope B := by
  by_cases hB : 3 ≤ B
  · exact
      selfridgeMaxima_le_of_QNegOne
        ((by norm_num only : (27 : ℝ) ≤ 31).trans (PseudoSquare.preciseEnvelope_ge_thirty_one hB))
        (PseudoSquare.QNegOne_le_preciseSaving B hGRH)
  · have he := precise_empty_boundary (Nat.lt_of_not_ge hB)
    simp only [he.1, he.2.1, he.2.2.1, he.2.2.2.1, Nat.cast_zero]
    have h0 := PseudoSquare.preciseSavingEnvelope_nonneg B
    exact ⟨h0, h0, h0, h0⟩

/-- Both classical trial maxima obey the sharp transfer of the complete precise-saving minimum.
Input: an endpoint at least three and GRH. Claim: the counts are at most (U-3)/2.
Proof: the envelope's thirty-one floor implies the sharp count transfer's entrance.
Role: retain every preceding and new candidate in the classical trial-cost bound. -/
theorem classicalTrials_le_preciseSaving {B : ℕ} (hB : 3 ≤ B)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ (PseudoSquare.preciseSavingEnvelope B - 3) / 2 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ (PseudoSquare.preciseSavingEnvelope B - 3) / 2 := by
  have h5 := (by norm_num only : (5 : ℝ) ≤ 31).trans (PseudoSquare.preciseEnvelope_ge_thirty_one hB)
  have hm := selfridgeMaxima_le_preciseSaving B hGRH
  exact ⟨classicalTrialCount_real_bound h5 hm.1, classicalTrialCount_real_bound h5 hm.2.2.1⟩

/-- Both classical trials satisfy the complete precise-saving bound on every natural endpoint.
Input: any endpoint and GRH. Claim: max(1,(U-3)/2) preserves the empty-domain count one.
Proof: apply the unconditional totalized count comparison to the full stopping bounds.
Role: the all-domain public trial interface without altering any scan convention. -/
theorem classicalTrials_le_preciseSavingAll (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ max 1 ((PseudoSquare.preciseSavingEnvelope B - 3) / 2) ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤
        max 1 ((PseudoSquare.preciseSavingEnvelope B - 3) / 2) := by
  have hm := selfridgeMaxima_le_preciseSaving B hGRH
  exact ⟨classicalTrialCount_real_max hm.1, classicalTrialCount_real_max hm.2.2.1⟩

/-- All four stopping maxima strictly improve the preceding fixed-cap bound in the window.
Input: GRH and an endpoint logarithm between forty-four and forty-six.
Claim: every stopping maximum is strictly below 4093.
Proof: the full new envelope lies below R31, which is below 3969.
Role: transfer the continuous whole-minimum improvement to actual Selfridge stops. -/
theorem selfridgeMaxima_lt_precise_window {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 44 ≤ Real.log B)
    (hU : Real.log B ≤ 46) :
    (classicalNegOneMaximum B : ℝ) < 4093 ∧
      (wheel30NegOneMaximum B : ℝ) < 4093 ∧
      (classicalNeOneMaximum B : ℝ) < 4093 ∧ (wheel30NeOneMaximum B : ℝ) < 4093 := by
  have hm := selfridgeMaxima_le_preciseSaving B hGRH
  have hx :=
    (PseudoSquare.preciseSavingEnvelope_le_prime31 B).trans_lt
      ((PseudoSquare.prime31Radius_lt_window hL hU).trans (by norm_num only : (3969 : ℝ) < 4093))
  exact ⟨hm.1.trans_lt hx, hm.2.1.trans_lt hx, hm.2.2.1.trans_lt hx, hm.2.2.2.trans_lt hx⟩

/-- Both classical trial maxima strictly improve the preceding cap's trial bound in the window.
Input: GRH and an endpoint logarithm between forty-four and forty-six.
Claim: both trial maxima are strictly below 2045.
Proof: use the sharp full-envelope transfer and the new cutoff below 4093.
Role: a continuous certified improvement in actual trial costs, including the original guards. -/
theorem classicalTrials_lt_precise_window {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 44 ≤ Real.log B)
    (hU : Real.log B ≤ 46) :
    (classicalNegOneTrialMaximum B : ℝ) < 2045 ∧ (classicalNeOneTrialMaximum B : ℝ) < 2045 := by
  have hB := (by norm_num only : (3 : ℕ) ≤ 750).trans (PseudoSquare.precise_window_input_lower hL)
  have ht := classicalTrials_le_preciseSaving hB hGRH
  have hx :=
    (PseudoSquare.preciseSavingEnvelope_le_prime31 B).trans_lt
      ((PseudoSquare.prime31Radius_lt_window hL hU).trans (by norm_num only : (3969 : ℝ) < 4093))
  exact ⟨by linarith only [ht.1, hx], by linarith only [ht.2, hx]⟩

end PseudoPrime.PrimeTestBounds.Selfridge
