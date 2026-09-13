/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.Selfridge.FirstStop
import PseudoPrime.PrimeTest.Selfridge.Reciprocity

/-!
# Selfridge witness interfaces for PrimeTest

These lemmas separate the production of a stopping witness from the
minimization of its stopping set.
-/

namespace PseudoPrime.PrimeTest

/-- Odd-prime witnesses whose Jacobi value is different from `1`. -/
def PrimeNeOneWitnessSet (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ jacobiSym n p ≠ 1}

/-- Odd-prime witnesses whose Jacobi value is `-1`. -/
def PrimeNegOneWitnessSet (n : ℕ) : Set ℕ :=
  {p | p.Prime ∧ Odd p ∧ jacobiSym n p = -1}

/-- A pure `-1` prime witness is also a `≠1` prime witness. -/
theorem PrimeNegOneWitnessSet.subset_primeNeOneWitnessSet (n : ℕ) :
    PrimeNegOneWitnessSet n ⊆ PrimeNeOneWitnessSet n := by
  intro p hp
  exact
    ⟨hp.1, hp.2.1, by
      rw [hp.2.2]; omega⟩

/-- Nonemptiness of the pure `-1` witness set implies nonemptiness of the `≠1` set. -/
theorem primeNeOneWitnessSet_nonempty_of_negOne {n : ℕ} (h : (PrimeNegOneWitnessSet n).Nonempty) :
    (PrimeNeOneWitnessSet n).Nonempty :=
  h.mono (PrimeNegOneWitnessSet.subset_primeNeOneWitnessSet n)

/-- The least odd-prime witness with Jacobi value different from `1`. -/
noncomputable def primeNeOneWitness (n : ℕ) (h : (PrimeNeOneWitnessSet n).Nonempty) : ℕ := by
  classical exact Nat.find h

/-- The least odd-prime witness with Jacobi value `-1`. -/
noncomputable def primeNegOneWitness (n : ℕ) (h : (PrimeNegOneWitnessSet n).Nonempty) : ℕ := by
  classical exact Nat.find h

/-- The least `≠1` witness belongs to its witness set. -/
theorem primeNeOneWitness_mem (n : ℕ) (h : (PrimeNeOneWitnessSet n).Nonempty) :
    primeNeOneWitness n h ∈ PrimeNeOneWitnessSet n := by classical exact Nat.find_spec h

/-- The least `-1` witness belongs to its witness set. -/
theorem primeNegOneWitness_mem (n : ℕ) (h : (PrimeNegOneWitnessSet n).Nonempty) :
    primeNegOneWitness n h ∈ PrimeNegOneWitnessSet n := by classical exact Nat.find_spec h

/-- Every `≠1` witness is at least the least `≠1` witness. -/
theorem primeNeOneWitness_le (n : ℕ) (h : (PrimeNeOneWitnessSet n).Nonempty) {p : ℕ}
    (hp : p ∈ PrimeNeOneWitnessSet n) : primeNeOneWitness n h ≤ p := by
  classical exact Nat.find_min' h hp

/-- Every `-1` witness is at least the least `-1` witness. -/
theorem primeNegOneWitness_le (n : ℕ) (h : (PrimeNegOneWitnessSet n).Nonempty) {p : ℕ}
    (hp : p ∈ PrimeNegOneWitnessSet n) : primeNegOneWitness n h ≤ p := by
  classical exact Nat.find_min' h hp

/-- The least `≠1` witness is no larger than the least `-1` witness. -/
theorem primeNeOneWitness_le_primeNegOneWitness (n : ℕ) (h : (PrimeNegOneWitnessSet n).Nonempty) :
    primeNeOneWitness n (primeNeOneWitnessSet_nonempty_of_negOne h) ≤ primeNegOneWitness n h := by
  apply primeNeOneWitness_le
  exact PrimeNegOneWitnessSet.subset_primeNeOneWitnessSet n (primeNegOneWitness_mem n h)

/-- Every member of a candidate predicate is odd. -/
def CandidateOdd (C : ℕ → Prop) : Prop :=
  ∀ ⦃i : ℕ⦄, C i → Odd i

/-- Classical Selfridge candidates are odd. -/
theorem isClassicalCandidate_odd : CandidateOdd isClassicalCandidate := by
  intro i hi
  exact hi.2

/-- Pure `-1` Wheel30 candidates are odd. -/
theorem isWheel30NegOneCandidate_odd : CandidateOdd isWheel30NegOneCandidate := by
  intro i hi
  rcases hi with hi | hi
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hi.2 with hi1 | hi7 | hi11 | hi13 | hi17 | hi19 | hi23 | hi29 <;> apply Nat.odd_iff.mpr <;>
    omega

/-- Factor-detecting Wheel30 candidates are odd. -/
theorem isWheel30NeOneCandidate_odd : CandidateOdd isWheel30NeOneCandidate := by
  intro i hi
  rcases hi with hi | hi
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hi.2 with hi1 | hi7 | hi11 | hi13 | hi17 | hi19 | hi23 | hi29 <;> apply Nat.odd_iff.mpr <;>
    omega

/-- A candidate with Jacobi value `-1` makes the pure stopping set nonempty. -/
theorem firstStopNegOneSet_nonempty_of_witness {C : ℕ → Prop} {n i : ℕ} (hi : C i)
    (hj : jacobiSym (selfridgeD i) n = -1) : (FirstStopNegOneSet C n).Nonempty := by
  exact ⟨i, hi, hj⟩

/-- A factor-free candidate with Jacobi value different from `1` makes the stopping set
nonempty. -/
theorem firstStopNeOneSet_nonempty_of_witness {C : ℕ → Prop} {n i : ℕ} (hi : C i) (hndvd : ¬n ∣ i)
    (hj : jacobiSym (selfridgeD i) n ≠ 1) : (FirstStopNeOneSet C n).Nonempty := by
  exact ⟨i, hi, hndvd, hj⟩

/-- A prime pure `-1` first-stop is an odd-prime Jacobi witness. -/
theorem primeNegOneWitnessSet_of_prime_mem_firstStopNegOneSet {C : ℕ → Prop} {n p : ℕ}
    (hC : CandidateOdd C) (hn : Odd n) (hp : p.Prime) (hstop : p ∈ FirstStopNegOneSet C n) :
    p ∈ PrimeNegOneWitnessSet n := by
  refine ⟨hp, hC hstop.1, ?_⟩
  rw [← jacobi_selfridgeD (hC hstop.1) hn]
  exact hstop.2

/-- A prime factor-detecting first-stop is an odd-prime `≠1` witness. -/
theorem primeNeOneWitnessSet_of_prime_mem_firstStopNeOneSet {C : ℕ → Prop} {n p : ℕ}
    (hC : CandidateOdd C) (hn : Odd n) (hp : p.Prime) (hstop : p ∈ FirstStopNeOneSet C n) :
    p ∈ PrimeNeOneWitnessSet n := by
  refine ⟨hp, hC hstop.1, ?_⟩
  rw [← jacobi_selfridgeD (hC hstop.1) hn]
  exact hstop.2.2

/-- An odd-prime `-1` witness in the candidate set is a pure stopping candidate. -/
theorem mem_firstStopNegOneSet_of_mem_primeNegOneWitnessSet {C : ℕ → Prop} {n p : ℕ} (hn : Odd n)
    (hCp : C p) (hp : p ∈ PrimeNegOneWitnessSet n) : p ∈ FirstStopNegOneSet C n := by
  refine ⟨hCp, ?_⟩
  rw [jacobi_selfridgeD hp.2.1 hn]
  exact hp.2.2

/-- An odd-prime `≠1` witness in the candidate set is factor-detecting when not divisible by
`n`. -/
theorem mem_firstStopNeOneSet_of_mem_primeNeOneWitnessSet {C : ℕ → Prop} {n p : ℕ} (hn : Odd n)
    (hCp : C p) (hndvd : ¬n ∣ p) (hp : p ∈ PrimeNeOneWitnessSet n) : p ∈ FirstStopNeOneSet C n := by
  refine ⟨hCp, hndvd, ?_⟩
  rw [jacobi_selfridgeD hp.2.1 hn]
  exact hp.2.2

/-- If the pure first-stop is prime, the least `-1` witness is no larger than it. -/
theorem primeNegOneWitness_le_firstStopNegOne_of_prime {C : ℕ → Prop} {n : ℕ} (hC : CandidateOdd C)
    (hn : Odd n) (hw : (PrimeNegOneWitnessSet n).Nonempty) (hs : (FirstStopNegOneSet C n).Nonempty)
    (hp : (firstStopNegOne C n hs).Prime) : primeNegOneWitness n hw ≤ firstStopNegOne C n hs := by
  apply primeNegOneWitness_le
  exact primeNegOneWitnessSet_of_prime_mem_firstStopNegOneSet hC hn hp (firstStopNegOne_mem C n hs)

/-- If the factor-detecting first-stop is prime, the least `≠ 1` witness is no larger than it. -/
theorem primeNeOneWitness_le_firstStopNeOne_of_prime {C : ℕ → Prop} {n : ℕ} (hC : CandidateOdd C)
    (hn : Odd n) (hw : (PrimeNeOneWitnessSet n).Nonempty) (hs : (FirstStopNeOneSet C n).Nonempty)
    (hp : (firstStopNeOne C n hs).Prime) : primeNeOneWitness n hw ≤ firstStopNeOne C n hs := by
  apply primeNeOneWitness_le
  exact primeNeOneWitnessSet_of_prime_mem_firstStopNeOneSet hC hn hp (firstStopNeOne_mem C n hs)

/-- If the least `-1` witness is a candidate, the pure first-stop is no larger than it. -/
theorem firstStopNegOne_le_primeNegOneWitness {C : ℕ → Prop} {n : ℕ} (hn : Odd n)
    (hw : (PrimeNegOneWitnessSet n).Nonempty) (hs : (FirstStopNegOneSet C n).Nonempty)
    (hC : C (primeNegOneWitness n hw)) : firstStopNegOne C n hs ≤ primeNegOneWitness n hw := by
  apply firstStopNegOne_le
  exact mem_firstStopNegOneSet_of_mem_primeNegOneWitnessSet hn hC (primeNegOneWitness_mem n hw)

/-- If the least `≠ 1` witness is a candidate and avoids `n`, the first-stop is no larger. -/
theorem firstStopNeOne_le_primeNeOneWitness {C : ℕ → Prop} {n : ℕ} (hn : Odd n)
    (hw : (PrimeNeOneWitnessSet n).Nonempty) (hs : (FirstStopNeOneSet C n).Nonempty)
    (hC : C (primeNeOneWitness n hw)) (hndvd : ¬n ∣ primeNeOneWitness n hw) :
    firstStopNeOne C n hs ≤ primeNeOneWitness n hw := by
  apply firstStopNeOne_le
  exact mem_firstStopNeOneSet_of_mem_primeNeOneWitnessSet hn hC hndvd (primeNeOneWitness_mem n hw)

end PseudoPrime.PrimeTest
