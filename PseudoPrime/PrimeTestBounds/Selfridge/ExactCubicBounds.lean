/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.CubicConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.ExactCubicJacobiBounds

/-! # Selfridge bounds with exact quadratic conductor and exclusion costs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH, the classical factor-detecting and pure negative stopping magnitudes
obey the exact-conductor cubic bound. Transfer the actual negative odd-prime witness
and absorb the small exceptions using the bound of at least 27.
The factor-detecting stop remains no larger than the negative stop. -/
theorem classicalSelfridgeD_cubic_exact_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
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
        PseudoSquare.cubicExactConductorBound bridge := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := PseudoSquare.primeNegOneWitness_le_cubic_exact bridge hGRH hw
  exact
    ⟨classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_firstStopNegOne_natAbs_cast hn hns,
      classicalSelfridgeD_neg_natAbs_le_of_prime_witness_bound hn hns hw
        (PseudoSquare.cubicExactConductorBound_ge27 bridge) hb⟩

/-- Under GRH, both Wheel30 stopping magnitudes obey the same exact cubic bound.
Rewrite the candidate scans by their unconditional equality with the classical scans.
This preserves the actual conductor and prime-two cost in the public stopping API. -/
theorem wheel30SelfridgeD_cubic_exact_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
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
        PseudoSquare.cubicExactConductorBound bridge := by
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns),
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    classicalSelfridgeD_cubic_exact_bound bridge hGRH

end PseudoPrime.PrimeTestBounds.Selfridge
