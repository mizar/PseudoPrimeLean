/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalPoleFiniteEntrance
public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer
public import PseudoPrime.PseudoSquare.Bounds.FourPoleFiniteBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.CommonEndpointBounds
/-! # Explicit fourth-pole finite bounds for Selfridge stops -/

public section

namespace PseudoPrime.PrimeTestBounds.Selfridge
/-- The fourth-pole witness bound at the explicit logarithmic entrance exceeds 27,
so the exceptional small Selfridge discriminants are absorbed. -/
theorem fourPole_finite_bound_ge_twenty_seven {n : ℕ} (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    27 ≤ (39 / 50 : ℝ) * (Real.log n) ^ 2 := by
  have hL10 : 10 ≤ Real.log n := by norm_num only at hL; linarith only [hL]
  nlinarith only [sq_nonneg (Real.log n - 10), hL10]

/-- Under GRH and `log n ≥ 10^18`, both classical and Wheel30 pure negative
Selfridge discriminant magnitudes are at most `(39/50)(log n)^2`.
Transfer the certified least negative Jacobi witness bound. -/
theorem selfridgeNegOne_fourPole_finite {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
      (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
        (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
      (39 / 50 : ℝ) * (Real.log n) ^ 2 ∧
    ((PrimeTest.selfridgeD
      (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
        (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
      (39 / 50 : ℝ) * (Real.log n) ^ 2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  exact selfridgeNegOneMagnitudes_le_of_prime_witness_bound hn hns hw
    (fourPole_finite_bound_ge_twenty_seven hL)
    (LLS.PaperStatements.fourPole_jacobi_finite_least hn hns hGRH hL hw)

/-- Under the same explicit entrance, both factor-detecting Selfridge magnitudes
obey the fourth-pole bound. Transfer the least non-one witness, which is no larger
than the least negative witness. -/
theorem selfridgeNeOne_fourPole_finite {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (10 : ℝ) ^ 18 ≤ Real.log n) :
    ((PrimeTest.selfridgeD
      (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
      (39 / 50 : ℝ) * (Real.log n) ^ 2 ∧
    ((PrimeTest.selfridgeD
      (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
        (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs : ℝ) ≤
      (39 / 50 : ℝ) * (Real.log n) ^ 2 := by
  let hw := NumberTheory.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  have hb := LLS.PaperStatements.fourPole_jacobi_finite_least hn hns hGRH hL hw
  have he : (NumberTheory.primeNeOneWitness n
      (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hw) : ℝ) ≤
      (NumberTheory.primeNegOneWitness n hw : ℝ) :=
    Nat.cast_le.mpr (NumberTheory.primeNeOneWitness_le_primeNegOneWitness n hw)
  exact selfridgeNeOneMagnitudes_le_of_prime_witness_bound hn hns
    (NumberTheory.primeNeOneWitnessSet_nonempty_of_negOne hw)
    ((by norm_num only : (15 : ℝ) ≤ 27).trans
      (fourPole_finite_bound_ge_twenty_seven hL)) (he.trans hb)
/-- Under GRH, all four Selfridge stopping maxima obey the full-domain fourth-pole
cumulative candidate, including empty domains. Absorb the exceptional cap 27. -/
theorem selfridgeMaxima_le_fourPole (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleCumulativeBound B ∧
      (wheel30NegOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleCumulativeBound B ∧
      (classicalNeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleCumulativeBound B ∧
      (wheel30NeOneMaximum B : ℝ) ≤ PseudoSquare.fourPoleCumulativeBound B := by
  have h27 : (27 : ℝ) ≤ PseudoSquare.fourPoleCumulativeBound B :=
    (by norm_num only : (27 : ℝ) ≤ (9999 / 10000) * ((10 : ℝ) ^ 18) ^ 2).trans
      (le_max_left _ _)
  exact selfridgeMaxima_le_of_QNegOne h27
    (PseudoSquare.witnessMaxima_le_fourPole B hGRH).1

/-- Under GRH, both classical trial maxima obey the fourth-pole cumulative
candidate divided by two plus one, at every natural endpoint. -/
theorem classicalTrials_le_fourPole (B : ℕ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ PseudoSquare.fourPoleCumulativeBound B / 2 + 1 ∧
      (classicalNeOneTrialMaximum B : ℝ) ≤ PseudoSquare.fourPoleCumulativeBound B / 2 + 1 := by
  have h := selfridgeMaxima_le_fourPole B hGRH
  have hn := classicalTrialCountThrough_real_le (classicalNegOneMaximum B)
  have he := classicalTrialCountThrough_real_le (classicalNeOneMaximum B)
  exact ⟨hn.trans (by linarith only [h.1]), he.trans (by linarith only [h.2.2.1])⟩

end PseudoPrime.PrimeTestBounds.Selfridge
