/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.TruncatedCubicJacobiBounds
public import PseudoPrime.PrimeTestBounds.Selfridge.WitnessTransfer

/-! # Selfridge bounds from cutoff-localized cubic witness radii -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- A localized cubic cutoff X≥27 bounds both classical and Wheel30 pure
negative Selfridge discriminant magnitudes under GRH. First bound the least
negative odd-prime witness, then use the generic stopping-value transfer.
The exclusion cost charges only prime factors at most X. -/
theorem selfridgeNegOneMagnitudes_le_of_truncated_cubic_radius {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {G E X : ℝ}
    (hlog : Real.log (NumberTheory.complexQuadraticCharacter n hn).conductor ≤ G)
    (hcost :
      LLS.PaperStatements.truncatedCharacterExclusionCost
          (NumberTheory.primitiveQuadraticCharacter n hn) (2 * n) X ≤
        E)
    (hbound : (LLS.PaperStatements.tightCubicExclusionRadius G E) ^ 2 ≤ X) (h27 : 27 ≤ X) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        X ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n
                (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        X := by
  exact
    selfridgeNegOneMagnitudes_le_of_prime_witness_bound hn hns hw h27
      (PseudoSquare.primeNegOneWitness_le_of_truncated_cubic_radius (hns := hns) hGRH hw hlog hcost
        hbound)

end PseudoPrime.PrimeTestBounds.Selfridge
