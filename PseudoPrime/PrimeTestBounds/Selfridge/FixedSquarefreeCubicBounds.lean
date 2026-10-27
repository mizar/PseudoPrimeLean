/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.FixedSquarefreeCubicWitnesses
public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer

/-! # Selfridge bounds independent of large square factors -/

public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- For an odd nonsquare n=s²d with squarefree d>1, GRH and the absence of
negative prime divisors of s below the fixed d radius bound both classical
and Wheel30 pure negative discriminant magnitudes. Transfer the least
negative prime bound and discharge the small-prime exception automatically. -/
theorem selfridgeNegOneMagnitudes_le_fixed_squarefree_family {n d s : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hd : 1 < d) (hsf : Squarefree d) (hdec : s ^ 2 * d = n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty)
    (hlarge :
      ∀ p : ℕ,
        p.Prime → p ∣ s → jacobiSym d p = -1 → PseudoSquare.fixedSquarefreeCubicBound d < p) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.fixedSquarefreeCubicBound d ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.fixedSquarefreeCubicBound d := by
  exact
    selfridgeNegOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (PseudoSquare.twenty_seven_le_fixedSquarefreeCubicBound d)
      (PseudoSquare.primeNegOneWitness_le_fixed_squarefree_family hn hns hd hsf hdec hGRH hw hlarge)

/-- For an odd nonsquare n=s²d with squarefree d>1, GRH and the absence of
negative prime divisors of s below the fixed d radius bound both classical
and Wheel30 factor-detecting discriminant magnitudes. Transfer the least
non-one prime bound and discharge the small-prime exception automatically. -/
theorem selfridgeNeOneMagnitudes_le_fixed_squarefree_family {n d s : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hd : 1 < d) (hsf : Squarefree d) (hdec : s ^ 2 * d = n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty)
    (hlarge :
      ∀ p : ℕ,
        p.Prime → p ∣ s → jacobiSym d p = -1 → PseudoSquare.fixedSquarefreeCubicBound d < p) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.fixedSquarefreeCubicBound d ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        PseudoSquare.fixedSquarefreeCubicBound d := by
  have h15 : (15 : ℝ) ≤ PseudoSquare.fixedSquarefreeCubicBound d :=
    (by norm_num only : (15 : ℝ) ≤ 27).trans
      (PseudoSquare.twenty_seven_le_fixedSquarefreeCubicBound d)
  exact
    selfridgeNeOneMagnitudes_le_of_prime_witness_bound hn hns hw h15
      (PseudoSquare.primeNeOneWitness_le_fixed_squarefree_family hn hns hd hsf hdec hGRH hw hlarge)

end PseudoPrime.PrimeTestBounds.Selfridge
