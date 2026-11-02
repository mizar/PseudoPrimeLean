/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleAbelEntrance
public import PseudoPrime.PseudoSquare.Bounds.LogScaleBounds

/-!
# Actual quadratic witness maxima from the double-Abel fourth-pole entrances

Each row is lifted at one common logarithmic scale, including earlier inputs and empty
admissible domains. The negative and non-one witness meanings remain separate. This module
contains only actual/least/cumulative transfers and the exceptional stopping floor; other
selected candidates and whole-minimum comparisons belong to a downstream comparison leaf.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- Evaluate a certified row at the larger entrance or endpoint logarithm.
Input: a row and any natural endpoint. Output: its coefficient times the squared
common scale. This covers every earlier input before taking a cumulative maximum. -/
noncomputable def fourPoleAbelRowBound (f : LLS.PaperStatements.FourPoleAbelRow) (B : ℕ) : ℝ :=
  logScaleBound f.coefficient (f.rootEntrance ^ 2) B

/-- The minimum of the three actual double-Abel entrance candidates.
Input: any natural endpoint. Output: the smallest certified common-scale bound.
This retains both the earliest entrance and the strongest eventual coefficient. -/
noncomputable def fourPoleAbelBound (B : ℕ) : ℝ :=
  min (fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel777 B)
    (min (fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel78 B)
      (fourPoleAbelRowBound LLS.PaperStatements.fourPoleAbel79 B))

/-- Under GRH, every certified row bounds the complete negative-witness maximum.
Lift its closed least-witness theorem at a common upper logarithmic scale.
The endpoint may be zero; the general lifting interface includes the empty domain. -/
theorem QNegOne_le_fourPole_abel_row (f : LLS.PaperStatements.FourPoleAbelRow) (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleAbelRowBound f B := by
  exact
    QNegOne_le_logScaleBound ((by norm_num only : (0 : ℝ) ≤ 777 / 1000).trans f.coefficient_lower)
      (fun {_n} hn hns {_L} hL hlog hw ↦
        LLS.PaperStatements.fourPole_abel_scale_least f hn hns hGRH hL hlog hw)
      B

/-- Under GRH, the minimum of all three rows bounds every negative cumulative maximum.
Combine the three complete common-scale estimates.
This is the full-domain cumulative API for the improved analytic entrances. -/
theorem QNegOne_le_fourPole_abel (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleAbelBound B := by
  exact
    le_min (QNegOne_le_fourPole_abel_row _ B hGRH)
      (le_min (QNegOne_le_fourPole_abel_row _ B hGRH) (QNegOne_le_fourPole_abel_row _ B hGRH))

/-- Both Jacobi witness maxima obey the new three-row minimum under GRH.
Use the actual negative bound and inclusion into the non-one witness set.
This provides both meanings without treating a non-one theorem as a negative theorem. -/
theorem witnessMaxima_le_fourPole_abel (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (QNegOne B : ℝ) ≤ fourPoleAbelBound B ∧ (QNeOne B : ℝ) ≤ fourPoleAbelBound B := by
  exact
    ⟨QNegOne_le_fourPole_abel B hGRH,
      (Nat.cast_le.mpr (QNeOne_le_QNegOne B)).trans (QNegOne_le_fourPole_abel B hGRH)⟩

/-- Any certified row's endpoint value absorbs the exceptional stopping value 27.
The common scale exceeds 1682 and the coefficient exceeds 777/1000.
Square these nonnegative comparisons. This permits the unconditional Selfridge transfer. -/
theorem fourPole_abel_row_ge_twenty_seven (f : LLS.PaperStatements.FourPoleAbelRow) (B : ℕ) :
    (27 : ℝ) ≤ fourPoleAbelRowBound f B := by
  have hmax : (1682 : ℝ) ≤ max (f.rootEntrance ^ 2) (Real.log B) :=
    f.scale_lower.trans (le_max_left _ _)
  have h0 : 0 ≤ max (f.rootEntrance ^ 2) (Real.log B) :=
    (by norm_num only : (0 : ℝ) ≤ 1682).trans hmax
  have hs := (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 1682) h0).mpr hmax
  have hc :=
    mul_le_mul_of_nonneg_right f.coefficient_lower
      (sq_nonneg (max (f.rootEntrance ^ 2) (Real.log B)))
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 777 / 1000)
  change 27 ≤ f.coefficient * max (f.rootEntrance ^ 2) (Real.log B) ^ 2
  nlinarith only [hc, hm]

/-- The minimum of the three row values still absorbs the exceptional stopping value.
Combine the individual floors with the order property of a minimum.
This supplies the generic stopping-transfer hypothesis at every natural endpoint. -/
theorem fourPole_abel_ge_twenty_seven (B : ℕ) : (27 : ℝ) ≤ fourPoleAbelBound B := by
  exact
    le_min (fourPole_abel_row_ge_twenty_seven _ B)
      (le_min (fourPole_abel_row_ge_twenty_seven _ B) (fourPole_abel_row_ge_twenty_seven _ B))

/-- The actual least negative witness obeys a row evaluated at its own endpoint.
Under GRH, choose the larger certified entrance or input logarithm as the common scale.
This connects the numerical row to the canonical least-witness definition. -/
theorem leastWitness_le_fourPole_abel_row (f : LLS.PaperStatements.FourPoleAbelRow) {n : ℕ}
    (hn : Odd n) (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fourPoleAbelRowBound f n := by
  exact
    LLS.PaperStatements.fourPole_abel_scale_least f hn hns hGRH (le_max_left _ _) (le_max_right _ _)
      hw

/-- The actual least negative witness obeys the minimum of the three row values.
Under GRH, combine all three bounds for the same canonical witness.
This exposes the new selected analytic candidate at individual inputs. -/
theorem leastWitness_le_fourPole_abel {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fourPoleAbelBound n := by
  exact
    le_min (leastWitness_le_fourPole_abel_row _ hn hns hGRH hw)
      (le_min (leastWitness_le_fourPole_abel_row _ hn hns hGRH hw)
        (leastWitness_le_fourPole_abel_row _ hn hns hGRH hw))

/-- Under GRH, both actual least Jacobi witnesses obey the new candidate at one input.
The least non-one witness is at most the least negative witness for that same input.
This retains the two least-witness meanings in the pointwise public interface. -/
theorem leastWitnesses_le_fourPole_abel {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ fourPoleAbelBound n ∧
      (NumberTheory.primeNeOneWitness n (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hw) :
          ℝ) ≤
        fourPoleAbelBound n := by
  have h := leastWitness_le_fourPole_abel hn hns hGRH hw
  exact ⟨h, (Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le_primeNegOneWitness n hw)).trans h⟩

/-- Under GRH, an actual negative Jacobi prime lies below the three-row minimum.
Use canonical nonemptiness and the bounded actual least negative witness.
This closes the endpoint candidate with its original actual-prime interpretation. -/
theorem existsWitness_le_fourPole_abel {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p ∈ NumberTheory.primeNegOneWitnessSet n ∧ (p : ℝ) ≤ fourPoleAbelBound n := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  exact
    ⟨NumberTheory.primeNegOneWitness n hw, NumberTheory.primeNegOneWitness_mem n hw,
      leastWitness_le_fourPole_abel hn hns hGRH hw⟩

end PseudoPrime.PseudoSquare
