/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Selfridge.Composite
public import PseudoPrime.PrimeTest.Selfridge.Nonempty

/-!
# Unconditional prime Selfridge witness comparison
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
A classical factor-detecting first stop that is prime bounds the least neutral prime witness.
Assume odd `n`, nonempty prime-witness and classical stopping sets, and a prime `p` equal to
the classical first stop. Its membership supplies oddness and a signed Jacobi value different
from one; reciprocity makes it a neutral witness. Leastness then gives
`primeNeOneWitness n hw ≤ p`, linking discrete stopping values to prime-witness bounds.
-/
theorem primeNeOneWitness_le_classicalFirstStop_of_prime {n : ℕ} (hn : Odd n)
    (hw : (PrimeNeOneWitnessSet n).Nonempty)
    (hs : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) {p : ℕ} (hp : p.Prime)
    (hstop : p = firstStopNeOne isClassicalCandidate n hs) : primeNeOneWitness n hw ≤ p := by
  apply primeNeOneWitness_le n hw
  subst p
  have hmem := firstStopNeOne_mem isClassicalCandidate n hs
  refine ⟨hp, isClassicalCandidate_odd hmem.1, ?_⟩
  rw [← jacobi_selfridgeD (isClassicalCandidate_odd hmem.1) hn]
  exact hmem.2.2

/--
A prime classical pure-minus-one first stop bounds the least neutral minus-one prime witness.
Assume odd `n`, both nonempty sets, and prime `p` equal to the classical first stop.
Stopping-set membership and signed reciprocity place `p` in the neutral prime-witness set;
its least-element property proves the bound. The primality of the stop is essential here:
this theorem does not identify a general composite stopping candidate with a prime witness.
-/
theorem primeNegOneWitness_le_classicalFirstStop_of_prime {n : ℕ} (hn : Odd n)
    (hw : (PrimeNegOneWitnessSet n).Nonempty)
    (hs : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) {p : ℕ} (hp : p.Prime)
    (hstop : p = firstStopNegOne isClassicalCandidate n hs) : primeNegOneWitness n hw ≤ p := by
  apply primeNegOneWitness_le n hw
  subst p
  have hmem := firstStopNegOne_mem isClassicalCandidate n hs
  refine ⟨hp, isClassicalCandidate_odd hmem.1, ?_⟩
  rw [← jacobi_selfridgeD (isClassicalCandidate_odd hmem.1) hn]
  exact hmem.2

/--
Any admissible factor-detecting classical candidate bounds the least classical first stop.
Assume odd nonsquare `n`, classical candidate `i`, `¬n ∣ i`, and signed Jacobi value different
from one. Odd-nonsquare nonemptiness defines the first stop, and the remaining hypotheses
place `i` in its stopping set. Applying leastness supplies a direct candidate-to-stop bound.
-/
theorem firstStopNeOne_le_candidate {n i : ℕ} (hn : Odd n) (hns : ¬IsSquare n)
    (hi : isClassicalCandidate i) (hndvd : ¬n ∣ i) (hvalue : jacobiSym (selfridgeD i) n ≠ 1) :
    firstStopNeOne isClassicalCandidate n
        (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns) ≤
      i := by
  apply
    firstStopNeOne_le isClassicalCandidate n
      (classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn hns)
  exact ⟨hi, hndvd, hvalue⟩

end PseudoPrime.PrimeTest
