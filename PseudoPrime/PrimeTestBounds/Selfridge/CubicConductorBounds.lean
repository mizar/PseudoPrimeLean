/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer
public import PseudoPrime.PseudoSquare.Bounds.CubicNegativeSupportBounds
public import PseudoPrime.PseudoSquare.Bounds.CubicLinearJacobiBounds

/-! # Selfridge bounds from cubic conductor and square-factor witness estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH for an odd nonsquare n=s²d, both classical Selfridge stopping
magnitudes obey the negative-support cubic radius, with the factor-detecting
stop no larger than the pure negative stop. Absorb 27 using the radius bound
of at least 70. No finite-input verification is used. -/
theorem classicalSelfridgeD_cubic_negative_support_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
        (LLS.PaperStatements.cubicSquareFactorRadius
            (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
            (PseudoSquare.negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
          2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := PseudoSquare.primeNegOneWitness_le_cubic_negative_support bridge hGRH hw
  have hr :=
    (LLS.PaperStatements.cubicSquareFactorRadius_data
        (Real.log_natCast_nonneg (4 * bridge.squarefreePart))
        (PseudoSquare.negativeSquareFactorCost_nonneg bridge.squarefreePart bridge.squareFactor)).1
  exact
    ⟨classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_firstStopNegOne_natAbs_cast hn hns,
      classicalSelfridgeD_neg_natAbs_le_of_prime_witness_bound hn hns hw (by nlinarith only [hr])
        hb⟩

/-- Under GRH, both classical Selfridge stopping magnitudes are bounded by
the explicit linear envelope for n=s²d. Apply the generic witness transfer and
absorb 27 using the envelope lower bound. The factor-detecting stop is at most
the pure negative stop, yielding the stated chain. -/
theorem classicalSelfridgeD_cubic_linear_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
        LLS.PaperStatements.cubicSquareFactorLinearEnvelope
          (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) (Real.log n) := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := PseudoSquare.primeNegOneWitness_le_cubic_linear_envelope bridge hGRH hw
  have hr :=
    LLS.PaperStatements.cubicSquareFactorLinearEnvelope_ge
      (Real.log_natCast_nonneg (4 * bridge.squarefreePart)) (Real.log_natCast_nonneg n)
  exact
    ⟨classicalSelfridgeD_firstStopNeOne_natAbs_cast_le_firstStopNegOne_natAbs_cast hn hns,
      classicalSelfridgeD_neg_natAbs_le_of_prime_witness_bound hn hns hw (by linarith only [hr]) hb⟩

/-- Under GRH and the two explicit conductor cutoffs, both classical Selfridge
stopping magnitudes are at most (4/3+delta)log n. Compose the linear envelope
chain with its quantified coefficient estimate. The factor-detecting stop is
still no larger than the pure negative stop. -/
theorem classicalSelfridgeD_cubic_linear_coefficient {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hc₁ :
      8 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) ^ 2 ≤
        δ * Real.log n)
    (hc₂ :
      64 * ((10 / 13 : ℝ) * Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ) + 35) ^ 2 ≤
        δ ^ 2 * Real.log n) :
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
        (4 / 3 + δ) * Real.log n := by
  have h := classicalSelfridgeD_cubic_linear_bound bridge hGRH
  exact
    ⟨h.1,
      h.2.trans
        (LLS.PaperStatements.cubicSquareFactorLinearEnvelope_le_coefficient
          (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg n) hδ hc₁ hc₂)⟩

/-- The executable Wheel30 candidate scans satisfy the same negative-support
cubic bounds as the classical scans under GRH for n=s²d. Rewrite both stops
using their unconditional equality with the classical first stops. -/
theorem wheel30SelfridgeD_cubic_negative_support_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
        (LLS.PaperStatements.cubicSquareFactorRadius
            (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ))
            (PseudoSquare.negativeSquareFactorCost bridge.squarefreePart bridge.squareFactor)) ^
          2 := by
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns),
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    classicalSelfridgeD_cubic_negative_support_bound bridge hGRH

/-- The Wheel30 factor-detecting and pure negative stops satisfy the same
fixed-squarefree-part linear envelope under GRH. Transfer the proved classical
chain using the exact unconditional equality of both candidate scans. -/
theorem wheel30SelfridgeD_cubic_linear_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
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
        LLS.PaperStatements.cubicSquareFactorLinearEnvelope
          (Real.log ((4 * bridge.squarefreePart : ℕ) : ℝ)) (Real.log n) := by
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns),
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    classicalSelfridgeD_cubic_linear_bound bridge hGRH

end PseudoPrime.PrimeTestBounds.Selfridge
