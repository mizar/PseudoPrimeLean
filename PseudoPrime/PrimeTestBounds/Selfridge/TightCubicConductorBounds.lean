/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.CubicConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.TightCubicNegativeSupportBounds

/-! # Selfridge stopping values from the tight cubic negative witness bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH and the odd nonsquare decomposition, both classical Selfridge
stopping magnitudes are bounded by the tight cubic square-factor radius.
Apply the least negative-prime bound and absorb the exception 27 using the
radius lower bound 65. The factor-detecting stop remains no larger. -/
theorem classicalSelfridgeD_tight_cubic_negative_support_bound {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (LLS.PaperStatements.tightCubicSquareFactorRadius
            (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
            (PseudoSquare.negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
          2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := PseudoSquare.primeNegOneWitness_le_tight_cubic_negative_support bridge hGRH hw
  have hr :=
    (LLS.PaperStatements.tightCubicSquareFactorRadius_data
        (Real.log_natCast_nonneg (4 * bridge.squarefreePart))
        (PseudoSquare.negativeSquareFactorCost_nonneg bridge.squarefreePart bridge.squareFactor)).1
  exact
    ⟨classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_firstStopNegOne_natAbs_cast hn hns,
      classicalSelfridgeD_neg_natAbs_le_of_prime_witness_bound hn hns hw (by nlinarith only [hr])
        hb⟩

/-- For odd nonsquare n=d*s² under GRH, the Wheel30 factor-detecting and
pure negative stopping magnitudes satisfy the tight cubic bound with 65/2.
Transfer the classical chain using exact equality of both candidate scans.
This connects the improved negative witness to the executable candidate family. -/
theorem wheel30SelfridgeD_tight_cubic_negative_support_bound {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (LLS.PaperStatements.tightCubicSquareFactorRadius
            (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
            (PseudoSquare.negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
          2 := by
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns),
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    classicalSelfridgeD_tight_cubic_negative_support_bound bridge hGRH

end PseudoPrime.PrimeTestBounds.Selfridge
