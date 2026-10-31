/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleSharpEntrance
public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer

/-! # Explicit fourth-pole finite bounds for Selfridge stops -/

public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- The fourth-pole witness bound at the explicit logarithmic entrance exceeds 27,
so the exceptional small Selfridge discriminants are absorbed. -/
theorem fourPole_sharp_bound_ge_twenty_seven {n : ℕ} (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    27 ≤ (777 / 1000 : ℝ) * (Real.log n) ^ 2 := by
  have hL10 : 10 ≤ Real.log n := by
    norm_num only at hL; linarith only [hL]
  nlinarith only [sq_nonneg (Real.log n - 10), hL10]

/-- Under GRH and `log n ≥ 10^18`, both classical and Wheel30 pure negative
Selfridge discriminant magnitudes are at most `(777/1000)(log n)^2`.
Transfer the certified least negative Jacobi witness bound. -/
theorem selfridgeNegOne_fourPole_sharp {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (777 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (777 / 1000 : ℝ) * (Real.log n) ^ 2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  exact
    selfridgeNegOneMagnitudes_le_of_prime_witness_bound hn hns hw
      (fourPole_sharp_bound_ge_twenty_seven hL)
      (LLS.PaperStatements.fourPole_sharp_jacobi_finite_least hn hns hGRH hL hw)

/-- Under the same explicit entrance, both factor-detecting Selfridge magnitudes
obey the fourth-pole bound. Transfer the least non-one witness, which is no larger
than the least negative witness. -/
theorem selfridgeNeOne_fourPole_sharp {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (777 / 1000 : ℝ) * (Real.log n) ^ 2 ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        (777 / 1000 : ℝ) * (Real.log n) ^ 2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := LLS.PaperStatements.fourPole_sharp_jacobi_finite_least hn hns hGRH hL hw
  have he :
    (NumberTheory.primeNeOneWitness n (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hw) :
        ℝ) ≤
      (NumberTheory.primeNegOneWitness n hw : ℝ) :=
    Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le_primeNegOneWitness n hw)
  exact
    selfridgeNeOneMagnitudes_le_of_prime_witness_bound hn hns
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hw)
      ((by norm_num only : (15 : ℝ) ≤ 27).trans (fourPole_sharp_bound_ge_twenty_seven hL))
      (he.trans hb)

end PseudoPrime.PrimeTestBounds.Selfridge
