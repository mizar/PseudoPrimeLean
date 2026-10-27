/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.Selfridge.Comparison
public import PseudoPrime.PrimeTest.Selfridge.WitnessBounds

/-! # Generic analytic-witness bounds for classical and Wheel30 Selfridge stops -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.Selfridge

/-- Any real upper bound X at least 27 for the least negative odd-prime witness
also bounds the classical pure negative Selfridge discriminant magnitude. Use
the unconditional max(27,witness) comparison. This generic transfer does not
assume GRH and can accept any subsequent analytic witness estimate. -/
theorem classicalSelfridgeD_neg_natAbs_le_of_prime_witness_bound {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {X : ℝ}
    (h27 : 27 ≤ X) (hb : (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ X) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      X := by
  let hs := PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns
  have hstop := PrimeTest.classicalFirstStopNegOne_le_max_twenty_seven_primeWitness hn hw hs
  have hstopR : (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n hs : ℝ) ≤ X :=
    (by exact_mod_cast hstop : _ ≤ max 27 (NumberTheory.primeNegOneWitness n hw : ℝ)).trans
      (max_le h27 hb)
  simpa only [PrimeTest.selfridgeD_natAbs] using hstopR

/-- Any real bound X at least 15 for the least non-one odd-prime witness
bounds the classical factor-detecting discriminant magnitude. Use the exact
max(15,witness) comparison and rewrite the signed discriminant magnitude.
No GRH is required; zero-valued witnesses remain available in this transfer. -/
theorem classicalSelfridgeD_ne_natAbs_le_of_prime_witness_bound {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) {X : ℝ} (h15 : 15 ≤ X)
    (hb : (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ X) :
    ((PrimeTest.selfridgeD
            (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
              (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
        ℝ) ≤
      X := by
  let hs := PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns
  have hstop := PrimeTest.classicalFirstStopNeOne_le_max_fifteen_primeWitness hn.pos hn hns hw hs
  have hstopR : (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n hs : ℝ) ≤ X :=
    (by exact_mod_cast hstop : _ ≤ max 15 (NumberTheory.primeNeOneWitness n hw : ℝ)).trans
      (max_le h15 hb)
  simpa only [PrimeTest.selfridgeD_natAbs] using hstopR

/-- A negative odd-prime witness bound X>=27 controls both classical and
Wheel30 pure negative discriminant magnitudes. Apply the generic classical
transfer and the unconditional equality of the two first stops.
This accepts arbitrary later analytic bounds without changing their hypotheses. -/
theorem selfridgeNegOneMagnitudes_le_of_prime_witness_bound {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty) {X : ℝ} (h27 : 27 ≤ X)
    (hb : (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ X) :
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
  have hc := classicalSelfridgeD_neg_natAbs_le_of_prime_witness_bound hn hns hw h27 hb
  refine ⟨hc, ?_⟩
  simpa only [PrimeTest.firstStopNegOne_wheel30_eq_classical hn
        (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn hns)] using
    hc

/-- A non-one odd-prime witness bound X>=15 controls both classical and
Wheel30 factor-detecting magnitudes. Apply the generic non-one transfer and
the unconditional equality of both scans. This preserves earlier entrance
conditions available only for zero-or-negative witnesses. -/
theorem selfridgeNeOneMagnitudes_le_of_prime_witness_bound {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty) {X : ℝ} (h15 : 15 ≤ X)
    (hb : (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ X) :
    ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n
                (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        X ∧
      ((PrimeTest.selfridgeD
              (PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n
                (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns))).natAbs :
          ℝ) ≤
        X := by
  have hc := classicalSelfridgeD_ne_natAbs_le_of_prime_witness_bound hn hns hw h15 hb
  refine ⟨hc, ?_⟩
  simpa only [PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn hns
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
        (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)] using
    hc

end PseudoPrime.PrimeTestBounds.Selfridge
