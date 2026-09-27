/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.Selfridge.Composite
import PseudoPrime.PrimeTest.Selfridge.Nonempty

/-!
# Unconditional prime Selfridge witness comparison
-/

namespace PseudoPrime.PrimeTest

/-- A prime classical `≠1` stop is at least the least neutral `≠1` prime witness. -/
theorem primeNeOneWitness_le_classicalFirstStop_of_prime {n : ℕ} (hn : Odd n)
    (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) {p : ℕ}
    (hp : p.Prime) (hstop : p = firstStopNeOne isClassicalCandidate n hs) :
    primeNeOneWitness n hw ≤ p := by
  apply primeNeOneWitness_le n hw
  subst p
  have hmem := firstStopNeOne_mem isClassicalCandidate n hs
  refine ⟨hp, isClassicalCandidate_odd hmem.1, ?_⟩
  rw [← jacobi_selfridgeD (isClassicalCandidate_odd hmem.1) hn]
  exact hmem.2.2

/-- A prime classical pure `-1` stop is at least the least neutral `-1` prime witness. -/
theorem primeNegOneWitness_le_classicalFirstStop_of_prime {n : ℕ} (hn : Odd n)
    (hw : (PrimeNegOneWitnessSet n).Nonempty)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) {p : ℕ}
    (hp : p.Prime) (hstop : p = firstStopNegOne isClassicalCandidate n hs) :
    primeNegOneWitness n hw ≤ p := by
  apply primeNegOneWitness_le n hw
  subst p
  have hmem := firstStopNegOne_mem isClassicalCandidate n hs
  refine ⟨hp, isClassicalCandidate_odd hmem.1, ?_⟩
  rw [← jacobi_selfridgeD (isClassicalCandidate_odd hmem.1) hn]
  exact hmem.2

/-- Any admissible rejecting candidate bounds the least classical stopping value. -/
theorem firstStopNeOne_le_candidate {n i : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hi : isClassicalCandidate i) (hndvd : ¬n ∣ i)
    (hvalue : jacobiSym (selfridgeD i) n ≠ 1) :
    firstStopNeOne isClassicalCandidate n
        (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) ≤
      i := by
  apply
    firstStopNeOne_le isClassicalCandidate n
      (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
  exact ⟨hi, hndvd, hvalue⟩


end PseudoPrime.PrimeTest
