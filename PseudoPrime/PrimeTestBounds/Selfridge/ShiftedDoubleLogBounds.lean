/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.AnalyticWitnessBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.OddMidscaleBounds
public import PseudoPrime.PseudoSquare.Bounds.ShiftedOddEndpointDoubleLogBounds

/-! # Selfridge non-one stopping magnitudes with correction constant 37/5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH for an odd nonsquare n with log n≥96, the two factor-detecting
Selfridge scans stop within the squared 37/5 double-log radius. Transfer
the improved least odd-prime non-one witness and absorb the exception 15
using the root lower bound 94. -/
theorem selfridgeNeOneMagnitudes_le_shifted_double_log {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (Real.log n - 2 * Real.log (Real.log n) + 37 / 5) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (Real.log n - 2 * Real.log (Real.log n) + 37 / 5) ^ 2 := by
  let hw :=
    NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne
      (NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns)
  have hb := PseudoSquare.primeNeOneWitness_cast_le_shiftedDoubleLog hn hns hGRH hL hw
  have hr := (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data hL).1
  dsimp only [LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot] at hr
  exact
    selfridgeNeOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (by nlinarith only [hr, sq_nonneg (Real.log n - 2 * Real.log (Real.log n) + 37 / 5 - 94)]) hb

/-- Under GRH and log B≥96, both factor-detecting Selfridge maxima through B
are bounded by the squared 37/5 double-log radius. Apply the common ambient
QNeOne bound, including all smaller odd nonsquare inputs, and absorb fifteen.
This is a finite-maximum bound, not a pointwise substitution at each input. -/
theorem selfridgeNeOneMaxima_le_shifted_double_log {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log B) :
    (classicalNeOneMaximum B : ℝ) ≤ (Real.log B - 2 * Real.log (Real.log B) + 37 / 5) ^ 2 ∧
      (wheel30NeOneMaximum B : ℝ) ≤ (Real.log B - 2 * Real.log (Real.log B) + 37 / 5) ^ 2 := by
  have hr := (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data hL).1
  dsimp only [LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot] at hr
  have hb := PseudoSquare.QNeOne_le_shiftedDoubleLog hL hGRH
  exact selfridgeNeOneMaxima_le_of_QNeOne_bound (by nlinarith only [hr]) hb

/-- Under GRH and log B≥96, the classical factor-detecting trial maximum
through B is at most (T(log B)²-3)/2 for T(L)=L-2log L+37/5. Apply the
proved common stopping maximum and the sharp generic trial conversion.
The count is the number of Jacobi trials, not an operation count. -/
theorem classicalNeOneTrialMaximum_le_shifted_double_log {B : ℕ}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 96 ≤ Real.log B) :
    (classicalNeOneTrialMaximum B : ℝ) ≤
      ((Real.log B - 2 * Real.log (Real.log B) + 37 / 5) ^ 2 - 3) / 2 := by
  have hr := (LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot_data hL).1
  dsimp only [LLS.PaperStatements.shiftedOddEndpointDoubleLogRoot] at hr
  have hb := (selfridgeNeOneMaxima_le_shifted_double_log hGRH hL).1
  exact classicalTrialCountThrough_real_le_of_value_bound (by nlinarith only [hr]) hb

end PseudoPrime.PrimeTestBounds.Selfridge
