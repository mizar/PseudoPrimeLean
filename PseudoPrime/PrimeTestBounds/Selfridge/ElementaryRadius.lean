/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.Comparison
public import PseudoPrime.PrimeTestBounds.Selfridge.LogGRH
public import PseudoPrime.PseudoSquare.Bounds.RefinedElementaryBounds

/-!
# GRH elementary radius application
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/--
Under GRH, for odd nonsquare `n ≥ 3`, the absolute classical `≠1` stopping value is at most
the absolute pure `-1` stopping value, and the latter is at most
`(log(4n) + (24/5)*loglog(4n) + 3)²`.
The proof pairs the preceding absolute-value comparison with
`classicalD_negOne_elementary_GRH`, providing both pointwise
inequalities in one public theorem. Nonemptiness of the stopping sets is supplied internally.
-/
theorem classicalSelfridgeD_elementary_bound_explicit
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
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
        (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 3) ^ 2 := by
  have hleft := classicalD_neOne_le_negOne hn hns
  have hright := classicalD_negOne_elementary_GRH hGRH hn3 hn hns
  exact ⟨hleft, hright⟩

/-- Under GRH and odd nonsquare n≥3, the classical negative stopping magnitude
is at most the refined elementary radius. Compare the stop with max(27,least negative witness)
and absorb 27 into the radius. This transfers the improved quadratic bound to Selfridge. -/
theorem classicalD_negOne_refinedRadius_GRH
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      PseudoSquare.refinedElementaryRadius n := by
  let hw := PrimeTest.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn hns
  let hs := PrimeTest.classicalNegOneSet_nonempty_of_odd_nonsquare hn hns
  have hstop := PrimeTest.classicalFirstNegOne_le_max_27_primeWitness hn hw hs
  have hb := PseudoSquare.primeNegOneWitness_le_refinedElementaryRadius hn3 hn hns hGRH hw
  have hroot := PseudoSquare.refinedElementaryRoot_gt hn3
  have h27 : (27 : ℝ) ≤ PseudoSquare.refinedElementaryRadius n := by
    unfold PseudoSquare.refinedElementaryRadius
    nlinarith only [hroot]
  have hstopR :
    (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n hs : ℝ) ≤
      PseudoSquare.refinedElementaryRadius n :=
    (by exact_mod_cast hstop : _ ≤ (max 27 (PrimeTest.primeNegOneWitness n hw) : ℝ)).trans
      (max_le h27 hb)
  simpa only [PrimeTest.selfridgeD_natAbs] using hstopR

/-- Under GRH and odd nonsquare n≥3, the classical non-one stopping magnitude
is no larger than the negative stopping magnitude, and the latter is bounded by
(log(4n)+(24/5)log(log(4n))+2)². Combine the stopping-value comparison with the
refined negative-witness estimate. This is the explicit refined Selfridge envelope. -/
theorem classicalD_refined_elementary_GRH
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn3 : 3 ≤ n)
    (hn : Odd n) (hns : ¬IsSquare n) :
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
        (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 2) ^ 2 := by
  exact ⟨classicalD_neOne_le_negOne hn hns, classicalD_negOne_refinedRadius_GRH hGRH hn3 hn hns⟩

end PseudoPrime.PrimeTestBounds.Selfridge
