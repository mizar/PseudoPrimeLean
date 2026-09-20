/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Selfridge.Composite
import PseudoPrime.PrimeTest.Selfridge.Nonempty

/-!
# Witness bridges for the Selfridge/GRH integration layer

These lemmas connect a prime classical stopping value to the corresponding neutral odd-prime
witness.  The analytic Q bounds are deliberately not imported here.
-/

namespace PseudoPrime.SelfridgeBoundGrh

/-- A prime classical `≠1` stop is at least the least neutral `≠1` prime witness. -/
theorem primeNeOneWitness_le_classicalFirstStop_of_prime {n : ℕ} (hn : Odd n)
    (hw : (PrimeTest.PrimeNeOneWitnessSet n).Nonempty)
    (hs : (PrimeTest.FirstStopNeOneSet PrimeTest.isClassicalCandidate n).Nonempty) {p : ℕ}
    (hp : p.Prime) (hstop : p = PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n hs) :
    PrimeTest.primeNeOneWitness n hw ≤ p := by
  apply PrimeTest.primeNeOneWitness_le n hw
  subst p
  have hmem := PrimeTest.firstStopNeOne_mem PrimeTest.isClassicalCandidate n hs
  refine ⟨hp, PrimeTest.isClassicalCandidate_odd hmem.1, ?_⟩
  rw [← PrimeTest.jacobi_selfridgeD (PrimeTest.isClassicalCandidate_odd hmem.1) hn]
  exact hmem.2.2

/-- A prime classical pure `-1` stop is at least the least neutral `-1` prime witness. -/
theorem primeNegOneWitness_le_classicalFirstStop_of_prime {n : ℕ} (hn : Odd n)
    (hw : (PrimeTest.PrimeNegOneWitnessSet n).Nonempty)
    (hs : (PrimeTest.FirstStopNegOneSet PrimeTest.isClassicalCandidate n).Nonempty) {p : ℕ}
    (hp : p.Prime) (hstop : p = PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n hs) :
    PrimeTest.primeNegOneWitness n hw ≤ p := by
  apply PrimeTest.primeNegOneWitness_le n hw
  subst p
  have hmem := PrimeTest.firstStopNegOne_mem PrimeTest.isClassicalCandidate n hs
  refine ⟨hp, PrimeTest.isClassicalCandidate_odd hmem.1, ?_⟩
  rw [← PrimeTest.jacobi_selfridgeD (PrimeTest.isClassicalCandidate_odd hmem.1) hn]
  exact hmem.2

end PseudoPrime.SelfridgeBoundGrh
