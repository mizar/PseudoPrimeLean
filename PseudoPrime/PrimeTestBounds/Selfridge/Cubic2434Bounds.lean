/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.CubicConductorBounds
public import PseudoPrime.PseudoSquare.Bounds.Cubic2434JacobiBounds

/-! # Selfridge bounds retaining the improved cubic root and conductor budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Under GRH, both classical Selfridge stopping magnitudes obey the improved root
bound at the actual squarefree logarithm. Transfer the negative odd-prime witness,
absorbing the exceptional magnitudes using the proved lower bound of 27. -/
theorem classicalSelfridgeD_cubic2434_root_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.cubic2434RootBound bridge := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := PseudoSquare.primeNegOneWitness_le_cubic2434_root bridge hGRH hw
  exact
    ⟨classicalD_neOne_le_negOne hn hns,
      classicalD_neg_natAbs_le_of_primeWitness hn hns hw
        (PseudoSquare.cubic2434_root_ge_twenty_seven bridge) hb⟩

/-- Under GRH, both classical stopping magnitudes obey the displayed improved envelope.
Compose the root stopping estimate with the root-to-envelope comparison.
The factor-detecting stop remains no larger than the pure negative stop. -/
theorem classicalSelfridgeD_cubic2434_linear_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.cubic2434LinearBound bridge := by
  have h := classicalSelfridgeD_cubic2434_root_bound bridge hGRH
  exact ⟨h.1, h.2.trans (PseudoSquare.cubic2434_envelope_chain bridge).1⟩

/-- Under GRH and the single explicit conductor cutoff for delta>0, both classical
stopping magnitudes are at most (4/3+delta)log(n). Compose the root bound directly
with its quadratic absorption theorem; the displayed envelope is not used. -/
theorem classicalSelfridgeD_cubic2434_coefficient_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hc : 4 * (4 / 3 + δ) * (PseudoSquare.cubic2434Base bridge) ^ 2 / δ ^ 2 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (4 / 3 + δ) * Real.log n := by
  have h := classicalSelfridgeD_cubic2434_root_bound bridge hGRH
  exact ⟨h.1, h.2.trans (PseudoSquare.cubic2434_root_single_cutoff bridge hδ hc)⟩

/-- Under GRH, the Wheel30 factor-detecting and negative stopping magnitudes satisfy
the stated improved cubic bound. Rewrite both scans by their unconditional equality
with the classical scans, preserving the root, envelope or single-cutoff hypothesis. -/
theorem wheel30SelfridgeD_cubic2434_root_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30NeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.cubic2434RootBound bridge := by
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30NeOneSet_nonempty_of_odd_nonsquare hn hns),
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    classicalSelfridgeD_cubic2434_root_bound bridge hGRH

/-- Under GRH, the Wheel30 factor-detecting and negative stopping magnitudes satisfy
the stated improved cubic bound. Rewrite both scans by their unconditional equality
with the classical scans, preserving the root, envelope or single-cutoff hypothesis. -/
theorem wheel30SelfridgeD_cubic2434_linear_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30NeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.cubic2434LinearBound bridge := by
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30NeOneSet_nonempty_of_odd_nonsquare hn hns),
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    classicalSelfridgeD_cubic2434_linear_bound bridge hGRH

/-- Under GRH, the Wheel30 factor-detecting and negative stopping magnitudes satisfy
the stated improved cubic bound. Rewrite both scans by their unconditional equality
with the classical scans, preserving the root, envelope or single-cutoff hypothesis. -/
theorem wheel30SelfridgeD_cubic2434_coefficient_bound {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : NumberTheory.JacobiCharacterArithmeticData n hn hns)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {δ : ℝ} (hδ : 0 < δ)
    (hc : 4 * (4 / 3 + δ) * (PseudoSquare.cubic2434Base bridge) ^ 2 / δ ^ 2 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30NeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (4 / 3 + δ) * Real.log n := by
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30NeOneSet_nonempty_of_odd_nonsquare hn hns),
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30NegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    classicalSelfridgeD_cubic2434_coefficient_bound bridge hGRH hδ hc

end PseudoPrime.PrimeTestBounds.Selfridge
