/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleReducedEntrance
public import PseudoPrime.PseudoSquare.Bounds.LogScaleBounds
public import PseudoPrime.PseudoSquare.Bounds.FourPoleCommonBounds

/-! # Reduced fourth-pole entrances for quadratic witnesses

The three certified LLS rows share one cumulative lifting interface. Their minimum
covers every natural endpoint and supplies actual least witnesses. Numerical certificates
remain in LLS; this module owns only their quadratic-witness consumers and comparisons.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- A certified row evaluated at the endpoint's common logarithmic scale.
Input: certified fourth-pole data and any natural endpoint. Output: its squared-scale bound.
Role: lift the row's actual-prime theorem to the cumulative witness maximum. -/
noncomputable def fourPoleEntranceBound (f : LLS.PaperStatements.FourPoleEntry) (B : ℕ) : ℝ :=
  logScaleBound f.coefficient (f.rootEntrance ^ 2) B

/-- The minimum of the three certified reduced-entrance candidates.
Input: any natural endpoint. Output: the best of the three common-scale bounds.
Role: retain the early entrance and the strongest eventual coefficient simultaneously. -/
noncomputable def fourPoleReducedBound (B : ℕ) : ℝ :=
  min (fourPoleEntranceBound LLS.PaperStatements.fourPole777Entrance B)
    (min (fourPoleEntranceBound LLS.PaperStatements.fourPole78Entrance B)
      (fourPoleEntranceBound LLS.PaperStatements.fourPole79Entrance B))

/-- Each certified row bounds the complete negative-witness maximum under GRH.
Input: a row, any endpoint and GRH. Claim: all earlier odd nonsquares are covered.
Proof: lift the row's closed least-witness theorem at a common upper scale.
Role: provide all three candidates without an additional scalar-gap premise. -/
theorem QNegOne_le_fourPoleEntrance (f : LLS.PaperStatements.FourPoleEntry) (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleEntranceBound f B :=
  QNegOne_le_logScaleBound ((by norm_num only : (0 : ℝ) ≤ 777 / 1000).trans f.coefficient_lower)
    (fun {_n} hn hns {_L} hL hlog hw ↦
      LLS.PaperStatements.fourPole_reduced_scale_least f hn hns hGRH hL hlog hw)
    B

/-- GRH bounds the negative maximum by the best reduced-entrance row.
Input: any natural endpoint and GRH. Claim: the minimum remains a valid cumulative bound.
Proof: combine the three certified estimates. Role: public full-domain reduced candidate. -/
theorem QNegOne_le_fourPole_reduced (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleReducedBound B :=
  le_min (QNegOne_le_fourPoleEntrance _ B hGRH)
    (le_min (QNegOne_le_fourPoleEntrance _ B hGRH) (QNegOne_le_fourPoleEntrance _ B hGRH))

/-- Both Jacobi maxima obey the reduced fourth-pole candidate under GRH.
Input: any endpoint and GRH. Claim: negative and non-one maxima satisfy the same bound.
Proof: use inclusion of the witness sets. Role: quadratic and Selfridge consumers. -/
theorem witnessMaxima_le_fourPole_reduced (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleReducedBound B ∧ (QNeOne B : ℝ) ≤ fourPoleReducedBound B :=
  ⟨QNegOne_le_fourPole_reduced B hGRH,
    (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans (QNegOne_le_fourPole_reduced B hGRH)⟩

/-- Every certified row exceeds the small exceptional Selfridge cap.
Input: a row and any endpoint. Claim: its cumulative bound is at least twenty-seven.
Proof: use the common lower coefficient and entrance. Role: unconditional stopping transfer. -/
theorem fourPoleEntrance_ge_twenty_seven (f : LLS.PaperStatements.FourPoleEntry) (B : ℕ) :
    27 ≤ fourPoleEntranceBound f B := by
  change 27 ≤ f.coefficient * max (f.rootEntrance ^ 2) (Real.log B) ^ 2
  have hscale : (100000000 : ℝ) ≤ max (f.rootEntrance ^ 2) (Real.log B) :=
    (LLS.PaperStatements.fourPole_data_scale_lower f).trans (le_max_left _ _)
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 100000000)
          ((by norm_num only : (0 : ℝ) ≤ 100000000).trans hscale)).mpr
      hscale
  have hm :=
    mul_le_mul_of_nonneg_right f.coefficient_lower
      (sq_nonneg (max (f.rootEntrance ^ 2) (Real.log B)))
  nlinarith only [hs, hm]

/-- The minimum of the reduced rows still absorbs exceptional stopping values.
Input: any endpoint. Claim: the bound is at least twenty-seven.
Proof: each row has this floor. Role: all four Selfridge maxima and totalized trial counts. -/
theorem fourPole_reduced_ge_twenty_seven (B : ℕ) : 27 ≤ fourPoleReducedBound B :=
  le_min (fourPoleEntrance_ge_twenty_seven _ B)
    (le_min (fourPoleEntrance_ge_twenty_seven _ B) (fourPoleEntrance_ge_twenty_seven _ B))

/-- The reduced candidate never worsens the previous common-scale fourth-pole bound.
Input: any endpoint. Claim: lowering the entrance preserves or improves the old value.
Proof: use the coefficient-777/1000 row. Role: compatibility with the previous candidate. -/
theorem fourPole_reduced_le_common (B : ℕ) : fourPoleReducedBound B ≤ fourPoleScaleBound B := by
  apply (min_le_left _ _).trans
  change
    (777 / 1000 : ℝ) * max ((1200000 : ℝ) ^ 2) (Real.log B) ^ 2 ≤
      (777 / 1000 : ℝ) * max ((10 : ℝ) ^ 18) (Real.log B) ^ 2
  have hm :=
    max_le_max (by norm_num only : (1200000 : ℝ) ^ 2 ≤ (10 : ℝ) ^ 18) (le_refl (Real.log B))
  have hz : 0 ≤ max ((1200000 : ℝ) ^ 2) (Real.log B) := (sq_nonneg _).trans (le_max_left _ _)
  exact
    mul_le_mul_of_nonneg_left ((sq_le_sq₀ hz (hz.trans hm)).mpr hm)
      (by norm_num only : (0 : ℝ) ≤ 777 / 1000)

/-- The reduced candidate also preserves the former history-based bound.
Input: any endpoint. Claim: neither entrance improvement worsens the legacy candidate.
Proof: compose the two comparisons. Role: a direct legacy compatibility certificate. -/
theorem fourPole_reduced_le_legacy (B : ℕ) : fourPoleReducedBound B ≤ fourPoleCumulativeBound B :=
  (fourPole_reduced_le_common B).trans (fourPole_scale_le_legacy B)

/-- Above the earliest reduced entrance, the new candidate strictly beats coefficient four fifths.
Input: an endpoint logarithm at least nine hundred million.
Claim: the reduced bound is strictly below four fifths times the logarithm squared.
Proof: select the coefficient-79/100 row. Role: a certified winning logarithmic interval. -/
theorem fourPole_reduced_lt_smoothed {B : ℕ} (hL : 900000000 ≤ Real.log B) :
    fourPoleReducedBound B < (4 / 5 : ℝ) * Real.log B ^ 2 := by
  apply (min_le_right _ _).trans_lt
  apply (min_le_right _ _).trans_lt
  change (79 / 100 : ℝ) * max ((30000 : ℝ) ^ 2) (Real.log B) ^ 2 < (4 / 5 : ℝ) * Real.log B ^ 2
  have hE : (30000 : ℝ) ^ 2 ≤ Real.log B := by
    norm_num only
    exact hL
  rw [max_eq_right hE]
  exact
    mul_lt_mul_of_pos_right (by norm_num only : (79 / 100 : ℝ) < 4 / 5)
      (sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 900000000).trans_le hL))

/-- Each row also bounds the least witness at its own input endpoint.
Input: a certified row, an odd nonsquare, GRH and witness nonemptiness.
Claim: the least witness obeys the common-scale endpoint value.
Proof: select the maximum entrance or input logarithm. Role: actual minimum selection. -/
theorem leastWitness_le_fourPoleEntrance (f : LLS.PaperStatements.FourPoleEntry) {n : ℕ}
    (hn : Odd n) (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fourPoleEntranceBound f n :=
  LLS.PaperStatements.fourPole_reduced_scale_least f hn hns hGRH (le_max_left _ _)
    (le_max_right _ _) hw

/-- The least actual negative witness satisfies the minimum of all three reduced rows.
Input: an odd nonsquare, GRH and witness nonemptiness. Claim: the best row is valid.
Proof: combine the three bounds for the same least witness.
Role: expose the reduced minimum without choosing an arithmetic certificate externally. -/
theorem leastWitness_le_fourPole_reduced {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fourPoleReducedBound n :=
  le_min (leastWitness_le_fourPoleEntrance _ hn hns hGRH hw)
    (le_min (leastWitness_le_fourPoleEntrance _ hn hns hGRH hw)
      (leastWitness_le_fourPoleEntrance _ hn hns hGRH hw))

/-- An actual negative Jacobi prime satisfies the reduced minimum under GRH.
Input: an odd nonsquare and GRH. Claim: the witness set contains a prime below the minimum.
Proof: use unconditional nonemptiness and the bounded least witness.
Role: close the cumulative candidate with its actual-prime interface. -/
theorem existsWitness_le_fourPole_reduced {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ fourPoleReducedBound n :=
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  ⟨NumberTheory.primeNegOneWitness n hw, NumberTheory.primeNegOneWitness_mem n hw,
    leastWitness_le_fourPole_reduced hn hns hGRH hw⟩

end PseudoPrime.PseudoSquare
